from __future__ import annotations

import copy
import inspect
import json
import logging
import os
import re
import sys
import types
import webbrowser
from pathlib import Path
from typing import Any, Optional

from bs4 import BeautifulSoup

from .snapshot import snapshot


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
            self._build_result_html(func_frame.frame)
            self._open_html()

    def _build_result_html(self, func_frame: types.FrameType) -> None:
        """Build and write the Webstepper html to the output directory"""
        snapshot_tracer_dir = os.path.dirname(os.path.abspath(__file__))

        html_content = self._read_original_html(snapshot_tracer_dir)
        soup = BeautifulSoup(html_content, "html.parser")

        self._modify_bundle_import_path(snapshot_tracer_dir, soup)
        self._insert_data(soup, func_frame)
        self._write_generated_html(soup)

    def _open_html(self) -> None:
        """Open the generated HTML file in a web browser."""
        index_html = f"file://{os.path.join(self.output_directory, 'index.html')}"
        webbrowser.open(index_html, new=2)

    def _read_original_html(self, snapshot_tracer_dir: str) -> None:
        """Read the original Webstepper html"""
        original_index_html = os.path.join(snapshot_tracer_dir, "webstepper", "index.html")
        with open(original_index_html, "r") as file:
            html_content = file.read()
        return html_content

    def _modify_bundle_import_path(self, snapshot_tracer_dir: str, soup: BeautifulSoup) -> None:
        """Modify the bundle path to the absolute path to the bundle"""
        original_js_bundle = os.path.join(snapshot_tracer_dir, "webstepper", "index.bundle.js")
        soup.select("script")[0]["src"] = f"file://{original_js_bundle}"

    def _insert_data(self, soup: BeautifulSoup, func_frame: types.FrameType) -> None:
        """Insert the SVG array and code string into the Webstepper index HTML."""
        insert_script = (
            f"<script>window.codeText=`{self._get_code(func_frame)}` </script>\n"
            + f"<script>window.svgArray={json.dumps(self._snapshots)}</script>\n"
        )
        soup.select("script")[0].insert_before(BeautifulSoup(insert_script, "html.parser"))

    def _write_generated_html(self, soup: BeautifulSoup) -> None:
        """Write the generated Webstepper html to the output directory"""
        modified_index_html = os.path.join(self.output_directory, "index.html")
        with open(modified_index_html, "w") as file:
            file.write(str(soup))

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
