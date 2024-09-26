from __future__ import annotations

import inspect
import os
import re
import sys
import types
from typing import Any, Iterable, Optional

from python_ta.debug.snapshot import snapshot


class SnapshotManager:
    memory_viz_args: Optional[list[str]]
    memory_viz_version: str
    snapshot_counts: int
    include: Optional[Iterable[str | re.Pattern]]
    output_filepath: Optional[str]

    def __init__(
        self,
        memory_viz_args: Optional[list[str]] = None,
        memory_viz_version: str = "0.3.2",
        include: Optional[Iterable[str | re.Pattern]] = None,
        output_filepath: Optional[str] = None,
    ) -> None:
        if memory_viz_args is None:
            memory_viz_args = ["--roughjs-config", "seed=12345"]
        self.memory_viz_version = memory_viz_version
        self.memory_viz_args = memory_viz_args
        self.snapshot_counts = 0
        self.include = include

        if any("--output" in arg for arg in memory_viz_args):
            raise ValueError("Use the output_filepath argument to specify a different output path.")

        self.output_filepath = output_filepath if output_filepath else "."
        print(os.path.join(os.path.abspath(self.output_filepath), f"snapshot.svg"))

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        if event == "line" and frame.f_locals:
            memory_viz_args_copy = self.memory_viz_args.copy()
            memory_viz_args_copy.extend(
                [
                    "--output",
                    os.path.join(
                        os.path.abspath(self.output_filepath),
                        f"snapshot-{self.snapshot_counts}.svg",
                    ),
                ]
            )
            snapshot(
                include=self.include,
                save=True,
                memory_viz_args=memory_viz_args_copy,
                memory_viz_version=self.memory_viz_version,
            )
            self.snapshot_counts += 1

    def __enter__(self):
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda frame, event, arg: None)
        print(f"Wrote {self.snapshot_counts} snapshots to {self.output_filepath}")
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        sys.settrace(None)
        inspect.getouterframes(inspect.currentframe())[1].frame.f_trace = None
