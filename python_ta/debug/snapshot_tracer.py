from __future__ import annotations

import copy
import inspect
import json
import logging
import os
import re
import shutil
import sys
import types
import webbrowser
from typing import Any, Optional

from bs4 import BeautifulSoup

from .snapshot import snapshot


class SnapshotTracer:
    """
    A class used for snapshot-based debugging to visualize program memory at each line in the calling function.

    Instance attributes:
        output_directory: The directory where the memory model diagrams will be saved. Defaults to the current directory.
        open_webstepper: Opens the web-based visualizer
        _snapshot_to_line: A list of dictionaries that maps the code line number and the snapshot number
        _snapshot_args: A dictionary of keyword arguments to pass to the `snapshot` function.
    """

    output_directory: Optional[str]
    open_webstepper: bool
    _snapshot_to_line: dict[int, int]
    _snapshot_args: dict[str, Any]
    _saved_files: list[str]

    def __init__(
        self, output_directory: Optional[str] = None, open_webstepper: bool = False, **kwargs
    ) -> None:
        """Initialize a context manager for snapshot-based debugging.

        Args:
            output_directory: The directory to save the snapshots, defaulting to the current directory.
                **Note**: Use this argument instead of the `--output` flag in `memory_viz_args` to specify the output directory.
            **kwargs: All other keyword arguments are passed to `python.debug.snapshot`. Refer to the `snapshot` function for more details.
        """
        if sys.version_info < (3, 10, 0):
            logging.warning("You need Python 3.10 or later to use SnapshotTracer.")
        if any("--output" in arg for arg in kwargs.get("memory_viz_args", [])):
            raise ValueError(
                "Use the output_directory parameter to specify a different output path."
            )
        self._snapshot_to_line = {}
        self._snapshot_args = kwargs
        self._snapshot_args["memory_viz_args"] = copy.deepcopy(kwargs.get("memory_viz_args", []))
        self._snapshot_counts = 0
        self._saved_file_names = []
        self.output_directory = os.path.abspath(output_directory if output_directory else ".")
        self.open_webstepper = open_webstepper
        self._correct_line_numbers = []
        self._first_line = float("inf")

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Take a snapshot of the variables in the functions specified in `self.include`"""
        if self._first_line == float("inf"):
            self._first_line = frame.f_lineno
        self._correct_line_numbers.append(frame.f_lineno - self._first_line + 1)
        if event == "line" and frame.f_locals:
            filename = os.path.join(
                self.output_directory,
                f"snapshot-{self._snapshot_counts}.svg",
            )
            self._snapshot_args["memory_viz_args"].extend(["--output", filename])

            snapshot(
                save=True,
                **self._snapshot_args,
            )

            self._saved_file_names.append(filename)
            self._snapshot_to_line[self._snapshot_counts] = {
                "lineNumber": self._correct_line_numbers[self._snapshot_counts]
            }
            self._snapshot_counts += 1

    def __enter__(self):
        """Set up the trace function to take snapshots at each line of code."""
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda *_args: None)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        """Remove the trace function."""
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
        if self.open_webstepper:
            self._open_webstepper()

    def _open_webstepper(self):
        self._copy_webstepper_bundle()
        self._generate_svg_array_js()
        self._insert_svg_array_js_to_index()
        self._open_html()

    def _copy_webstepper_bundle(self):
        # TODO: we shouldn't copy the whole thing, this is a temporary solution
        # The other way is to only copy the html file, but we need to change the
        # script imports to absolute paths. Browser blocks that
        source_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "webstepper")
        destination_dir = os.path.join(self.output_directory, "webstepper")
        shutil.copytree(source_dir, destination_dir, dirs_exist_ok=True)

    def _generate_svg_array_js(self):
        for svg_filename in self._saved_file_names:
            svg_file_path = os.path.join(self.output_directory, svg_filename)
            snapshot_number = int(re.search(r"snapshot-(\d+)\.svg", svg_filename).group(1))

            with open(svg_file_path) as svg_file:
                svg_content = svg_file.read()
                self._snapshot_to_line[snapshot_number]["svg"] = svg_content

        svg_array_js_path = os.path.join(self.output_directory, "webstepper", "lineToSnapshot.js")
        with open(svg_array_js_path, "w") as svg_array_js_file:
            svg_array_js_content = f"window.svgArray = {json.dumps(self._snapshot_to_line)}"
            svg_array_js_file.write(svg_array_js_content)

    def _insert_svg_array_js_to_index(self):
        current_dir = os.path.dirname(os.path.abspath(__file__))
        original_index_html = os.path.join(current_dir, "webstepper", "index.html")

        with open(original_index_html, "r") as file:
            lines = file.readlines()

        html_content = "".join(lines)
        soup = BeautifulSoup(html_content, "html.parser")

        script_tags = soup.select("script")
        script_tags[0].insert_before(
            BeautifulSoup(f'<script src="lineToSnapshot.js"></script>\n', "html.parser")
        )

        destination_dir = os.path.join(self.output_directory, "webstepper")
        modified_index_html = os.path.join(destination_dir, "index.html")
        with open(modified_index_html, "w") as file:
            file.write(str(soup))

    def _open_html(self):
        index_html = f"file://{os.path.join(self.output_directory, 'webstepper', 'index.html')}"
        webbrowser.open(index_html, new=2)
