from __future__ import annotations

import base64
import copy
import inspect
import logging
import os
import socket
import sys
import warnings
from pathlib import Path
from typing import TYPE_CHECKING, Any, Optional

from jinja2 import Environment, FileSystemLoader

from ..util.servers.one_shot_server import open_html_in_browser
from .id_tracker import IDTracker
from .snapshot import snapshot, snapshot_to_json

if TYPE_CHECKING:
    import types


class SnapshotTracer:
    """
    A class used for snapshot-based debugging to visualize program memory at each line in the calling function.

    Instance attributes:
        webstepper: Opens the web-based visualizer.
        snapshots: A list of dictionaries that maps the code line number and corresponding MemoryViz JSON snapshot at each traced line.
        _webstepper_options: A dictionary of configuration options for the webstepper visualizer.
        _snapshot_args: A dictionary of keyword arguments to pass to the `snapshot` function.
        _first_line: Line number of the first line in the `with` block.
    """

    webstepper: bool
    _webstepper_options: dict[str, Any]
    _snapshots: list[dict[str, Any]]
    _snapshot_args: dict[str, Any]
    _first_line: int

    def __init__(
        self,
        output_directory: Optional[str] = None,
        webstepper: bool = False,
        webstepper_options: Optional[dict[str, Any]] = None,
        **kwargs,
    ) -> None:
        """Initialize a context manager for snapshot-based debugging.

        Args:
            output_directory: This argument is deprecated; previously used for file-based outputs.
            webstepper: Opens a MemoryViz Webstepper webpage to interactively visualize the resulting memory diagrams.
            webstepper_options: A dictionary of configuration options for the Webstepper visualizer when webstepper=True.
                Supported options:
                    line_context: Number of lines of context to show above and below the traced block in the Webstepper view if > 0.
            **kwargs: All other keyword arguments are passed to `python.debug.snapshot`. Refer to the `snapshot` function for more details.
        """
        if sys.version_info < (3, 10, 0):
            logging.warning("You need Python 3.10 or later to use SnapshotTracer.")
        if output_directory is not None:
            warnings.warn("The output_directory argument is deprecated.", DeprecationWarning)
        self._snapshots = []
        self._snapshot_args = kwargs
        self._snapshot_args["memory_viz_args"] = copy.deepcopy(kwargs.get("memory_viz_args", []))
        self._snapshot_args["exclude_frames"] = copy.deepcopy(kwargs.get("exclude_frames", []))
        self._snapshot_args["exclude_frames"].append("_trace_func")
        self.id_tracker = IDTracker()

        self.webstepper = webstepper
        self._webstepper_options = webstepper_options if webstepper_options is not None else {}
        if self._webstepper_options and not self.webstepper:
            warnings.warn(
                "webstepper_options have no effect when webstepper=False. Set webstepper=True to use webstepper_options.",
                UserWarning,
            )
        self._first_line = float("inf")

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Take a snapshot of the variables in the functions specified in `self.include`"""
        if self._first_line == float("inf"):
            self._first_line = frame.f_lineno
        if event == "line":
            snapshot_output = snapshot(
                id_tracker=self.id_tracker,
                **self._snapshot_args,
            )
            json_data = snapshot_to_json(snapshot_output, id_tracker=self.id_tracker)
            self._snapshots.append(
                {
                    "lineNumber": frame.f_lineno,
                    "memoryVizInput": json_data,
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

        code_text, start_line_number = self._get_code(func_frame)

        rendered_html = template.render(
            code_text=code_text,
            start_line_number=start_line_number,
            memory_viz_data=self._snapshots,
            bundle_content=bundle_content,
        )

        return rendered_html.encode("utf-8")

    def _serve_html(self, html_content: bytes) -> None:
        """Serve the HTML content using a one-shot server."""
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]

        open_html_in_browser(html_content, port)

    def _get_code(self, func_frame: types.FrameType) -> tuple[str, int]:
        """Retrieve and save the code string to be displayed in Webstepper.
        Return a tuple of (code_text, start_line_number) where start_line_number
        is the line number in the source file of the first line of the traced code.
        """
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

        line_context = self._webstepper_options.get("line_context", 0)
        if line_context > 0:
            startpoint = max(0, startpoint - line_context)
            endpoint = min(len(lst_str_lines) - 1, endpoint + line_context)

        start_line_number = max(1, self._first_line - line_context)

        return "\n".join(lst_str_lines[startpoint : endpoint + 1]), start_line_number

    @property
    def snapshots(self) -> list[dict[str, Any]]:
        """Return the snapshots taken at each line of code."""
        return self._snapshots
