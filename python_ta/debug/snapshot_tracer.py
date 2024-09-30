from __future__ import annotations

import copy
import inspect
import logging
import os
import sys
import types
from typing import Any, Optional

from .snapshot import snapshot


class SnapshotTracer:
    """
    A class used for snapshot-based debugging to visualize program memory at each line in the calling function.

    Instance attributes:
        include: A collection of function names, either as strings or regular expressions, whose variables will be captured.
        output_directory: The directory where the memory model diagrams will be saved. Defaults to the current directory.
    """

    output_directory: Optional[str]
    _snapshot_counts: int
    _snapshot_args: dict[str, Any]

    def __init__(self, output_directory: Optional[str] = None, **kwargs) -> None:
        """Initialize a SnapshotManager context manager for snapshot-based debugging.

        Args:
            output_directory: The directory to save the snapshots, defaulting to the current directory.
                **Note**: Use this argument instead of the `--output` flag in `memory_viz_args` to specify the output directory.
            **kwargs: All other keyword arguments are passed to `python.debug.snapshot`. Refer to the `snapshot` function for more details.
        """
        if sys.version_info < (3, 10, 0):
            logging.warning("You need Python 3.10 or later to use SnapshotManager.")
        if any("--output" in arg for arg in kwargs.get("memory_viz_args", [])):
            raise ValueError(
                "Use the output_directory parameter to specify a different output path."
            )
        self._snapshot_args = kwargs
        self._snapshot_args["memory_viz_args"] = copy.deepcopy(kwargs.get("memory_viz_args", []))
        self._snapshot_counts = 0
        self.output_directory = output_directory if output_directory else "."

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Take a snapshot of the variables in the functions specified in `self.include`"""
        if event == "line" and frame.f_locals:
            self._snapshot_args["memory_viz_args"].extend(
                [
                    "--output",
                    os.path.join(
                        os.path.abspath(self.output_directory),
                        f"snapshot-{self._snapshot_counts}.svg",
                    ),
                ]
            )
            snapshot(
                save=True,
                **self._snapshot_args,
            )
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
