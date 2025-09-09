from __future__ import annotations

import base64
import copy
import inspect
import json
import logging
import os
import socket
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Any, Optional

from jinja2 import Environment, FileSystemLoader

from ..util.servers.one_shot_server import open_html_in_browser
from .id_tracker import IDTracker
from .snapshot import snapshot

if TYPE_CHECKING:
    import types


class SnapshotTracer:
    """
    A class used for snapshot-based debugging to visualize program memory at each line in the calling function.

    Instance attributes:
        output_directory: The directory where the memory model diagrams will be saved. Defaults to the current directory.
        webstepper: Opens the web-based visualizer.
        _snapshots: A list of dictionaries that maps the code line number and the snapshot number.
        _snapshot_args: A dictionary of keyword arguments to pass to the `snapshot` function.
        _first_line: Line number of the first line in the `with` block.
    """

    output_directory: Optional[str]
    webstepper: bool
    _snapshots: list[dict[int, int]]
    _snapshot_args: dict[str, Any]
    _first_line: int

    def __init__(
        self,
        output_directory: Optional[str] = None,
        webstepper: bool = False,
        **kwargs,
    ) -> None:
        """Initialize a context manager for snapshot-based debugging.

        Args:
            output_directory: The directory to save the snapshots, defaulting to the current directory.
                **Note**: Use this argument instead of the `--output` flag in `memory_viz_args` to specify the output directory.
                The directory will be created if it does not exist.
            webstepper: Opens a MemoryViz Webstepper webpage to interactively visualize the resulting memory diagrams.
            **kwargs: All other keyword arguments are passed to `python.debug.snapshot`. Refer to the `snapshot` function for more details.
        """
        if sys.version_info < (3, 10, 0):
            logging.warning("You need Python 3.10 or later to use SnapshotTracer.")
        if any("--output" in arg for arg in kwargs.get("memory_viz_args", [])):
            raise ValueError(
                "Use the output_directory parameter to specify a different output path."
            )
        self._snapshots = []
        self._snapshot_args = kwargs
        self._snapshot_args["memory_viz_args"] = copy.deepcopy(kwargs.get("memory_viz_args", []))
        self._snapshot_args["exclude_frames"] = copy.deepcopy(kwargs.get("exclude_frames", []))
        self._snapshot_args["exclude_frames"].append("_trace_func")
        self.output_directory = os.path.abspath(output_directory if output_directory else ".")
        self.id_tracker = IDTracker()
        Path(self.output_directory).mkdir(parents=True, exist_ok=True)

        self.webstepper = webstepper
        self._first_line = float("inf")

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Take a snapshot of the variables in the functions specified in `self.include`"""
        if self._first_line == float("inf"):
            self._first_line = frame.f_lineno
        if event == "line":
            filename = os.path.join(
                self.output_directory,
                f"snapshot-{len(self._snapshots)}.svg",
            )
            self._snapshot_args["memory_viz_args"].extend(["--output", filename])

            snapshot(
                id_tracker=self.id_tracker,
                save=True,
                **self._snapshot_args,
            )

            self._add_svg_to_map(filename, frame.f_lineno)

    def _add_svg_to_map(self, filename: str, line: int) -> None:
        """Add the SVG in filename to self._snapshots"""
        with open(filename) as svg_file:
            svg_content = svg_file.read()
            self._snapshots.append(
                {
                    "lineNumber": line,
                    "svg": svg_content,
                }
            )

    def __enter__(self):
        """Set up the trace function to take snapshots at each line of code."""
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda *_args: None)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        """Remove the trace function. If webstepper=True, open a Webstepper webpage."""
        sys.settrace(None)
        func_frame = inspect.getouterframes(inspect.currentframe())[1]
        func_frame.frame.f_trace = None
        if self.webstepper:
            html_content = self._build_self_contained_html(func_frame.frame)
            self._serve_html(html_content)

    def _build_self_contained_html(self, func_frame: types.FrameType) -> bytes:
        """Build a self-contained HTML string with all assets inlined."""
        webstepper_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "webstepper")

        bundle_path = os.path.join(webstepper_dir, "index.bundle.js")
        with open(bundle_path, "r", encoding="utf-8") as f:
            bundle_content = f.read()

        image_replacements = {}
        for image_filename in ["99ee5c67fd0c522b4b6a.png", "fd6133fe40f4f90440d6.png"]:
            image_path = os.path.join(webstepper_dir, image_filename)
            with open(image_path, "rb") as f:
                image_data = f.read()
                base64_data = base64.b64encode(image_data).decode("utf-8")
                data_uri = f"data:image/png;base64,{base64_data}"
                image_replacements[image_filename] = data_uri

        for filename, data_uri in image_replacements.items():
            bundle_content = bundle_content.replace(filename, data_uri)

        template_loader = FileSystemLoader(webstepper_dir)
        template_env = Environment(loader=template_loader)
        template = template_env.get_template("webstepper_template.html.jinja")

        rendered_html = template.render(
            code_text=self._get_code(func_frame),
            svg_array=self._snapshots,
            bundle_content=bundle_content,
        )

        return rendered_html.encode("utf-8")

    def _serve_html(self, html_content: bytes) -> None:
        """Serve the HTML content using a one-shot server."""
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]

        open_html_in_browser(html_content, port)

    def _get_code(self, func_frame: types.FrameType) -> str:
        """Retrieve and save the code string to be displayed in Webstepper."""
        code_lines = inspect.cleandoc(inspect.getsource(func_frame))
        i = self._first_line - func_frame.f_code.co_firstlineno
        lst_str_lines = code_lines.splitlines()
        num_whitespace = len(lst_str_lines[i]) - len(lst_str_lines[i].lstrip())

        endpoint = len(lst_str_lines)
        startpoint = i
        while i < len(lst_str_lines):
            line = lst_str_lines[i]
            if (
                line.strip() != ""
                and not line.lstrip()[0] == "#"
                and not line[:num_whitespace].isspace()
            ):
                break
            if line.lstrip() != "" and len(line) - len(line.lstrip()) >= num_whitespace:
                lst_str_lines[i] = line[num_whitespace:]
            else:
                lst_str_lines[i] = line.lstrip()
            endpoint = i
            i += 1

        return "\n".join(lst_str_lines[startpoint : endpoint + 1])
