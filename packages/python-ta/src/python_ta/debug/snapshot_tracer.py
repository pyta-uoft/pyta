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
        _snapshot_args: A dictionary of keyword arguments to pass to the `snapshot` function.
        _start_lineno: Line number of the first line to be displayed in the code section of the Webstepper.
        _end_lineno: Line number of the last line to be displayed in the code section of the Webstepper.
        _origin_file: The absolute path of the module where SnapshotTracer is used.
        _module_source_lines: A list of strings representing the source code lines of the module where SnapshotTracer is used.
    """

    webstepper: bool
    _snapshots: list[dict[str, Any]]
    _snapshot_args: dict[str, Any]
    _start_lineno: int
    _end_lineno: int
    _origin_file: str | None
    _module_source_lines: list[str] | None

    def __init__(
        self,
        output_directory: Optional[str] = None,
        webstepper: bool = False,
        **kwargs,
    ) -> None:
        """Initialize a context manager for snapshot-based debugging.

        Args:
            output_directory: This argument is deprecated; previously used for file-based outputs.
            webstepper: Opens a MemoryViz Webstepper webpage to interactively visualize the resulting memory diagrams.
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
        self._start_lineno = sys.maxsize
        self._end_lineno = 0
        self._origin_file = None
        self._module_source_lines = None

    def _global_trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> Any:
        """Global trace function that handles 'call' events to determine which functions to trace into."""
        if event == "call":
            if self._origin_file is None:
                return None
            # Only trace functions in the same module as the calling function.
            called_file = os.path.normcase(os.path.abspath(frame.f_code.co_filename))
            if called_file == self._origin_file and frame.f_code.co_name not in (
                "_trace_func",
                "_global_trace_func",
            ):
                self._start_lineno = min(self._start_lineno, frame.f_code.co_firstlineno)
                self._end_lineno = max(
                    self._end_lineno,
                    frame.f_code.co_firstlineno + len(inspect.getsourcelines(frame)[0]) - 1,
                )
                # Return self._trace_func to trace into the called function, otherwise return None to skip tracing.
                return self._trace_func
            return None

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> Any:
        """Local trace function set on each frame to take a snapshot of the variables in the functions specified in `self.include`."""
        if event == "line":
            self._start_lineno = min(self._start_lineno, frame.f_lineno)
            self._end_lineno = max(self._end_lineno, frame.f_lineno)
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
        origin_file = func_frame.f_globals.get("__file__")
        self._origin_file = (
            os.path.normcase(os.path.abspath(origin_file)) if origin_file is not None else None
        )
        if self._origin_file is not None:
            self._module_source_lines = (
                Path(self._origin_file).read_text(encoding="utf-8").splitlines()
            )
        sys.settrace(self._global_trace_func)
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
            code_text=self._get_code(),
            start_line_number=self._start_lineno,
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

    def _get_code(self) -> str:
        """Retrieve and save the code string to be displayed in Webstepper."""
        if self._module_source_lines is None or self._start_lineno > self._end_lineno:
            return ""

        start_index = max(self._start_lineno - 1, 0)
        end_index = min(self._end_lineno, len(self._module_source_lines))
        return "\n".join(self._module_source_lines[start_index:end_index])

    @property
    def snapshots(self) -> list[dict[str, Any]]:
        """Return the snapshots taken at each line of code."""
        return self._snapshots
