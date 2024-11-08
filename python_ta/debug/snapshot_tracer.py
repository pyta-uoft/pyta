from __future__ import annotations

import copy
import inspect
import json
import logging
import os
import re
import sys
import types
from typing import Any, Optional

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
        self.output_directory = output_directory if output_directory else "."
        self.open_webstepper = open_webstepper

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Take a snapshot of the variables in the functions specified in `self.include`"""
        if event == "line" and frame.f_locals:
            filename = os.path.join(
                os.path.abspath(self.output_directory),
                f"snapshot-{self._snapshot_counts}.svg",
            )
            self._snapshot_args["memory_viz_args"].extend(["--output", filename])

            snapshot(
                save=True,
                **self._snapshot_args,
            )

            self._saved_file_names.append(filename)
            self._snapshot_to_line[self._snapshot_counts] = {"lineNumber": frame.f_lineno}
            self._snapshot_counts += 1

    def _output_svg_to_js(self):
        for filename in self._saved_file_names:
            path = os.path.join(self.output_directory, filename)
            # TODO: maybe there is a better way to do this
            snapshot_number = int(re.search(r"snapshot-(\d+)\.svg", filename).group(1))

            with open(path) as file:
                svg = file.read()
                self._snapshot_to_line[snapshot_number]["svg"] = svg

        jsPath = os.path.join(os.path.abspath(self.output_directory), "lineToSnapshot.js")
        with open(jsPath, "w") as file:
            line = f"window.svgArray = {json.dumps(self._snapshot_to_line)}"
            file.write(line)

    def __enter__(self):
        """Set up the trace function to take snapshots at each line of code."""
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda *_args: None)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        """Remove the trace function."""
        if self.open_webstepper:
            self._output_svg_to_js()
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
