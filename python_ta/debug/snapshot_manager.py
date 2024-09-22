import inspect
import json
import os
import shutil
import subprocess
import sys
import types
from typing import Any, List, Optional

from python_ta.debug.snapshot import snapshot, snapshot_to_json


# TODO: decide what control we want to give the user
class SnapshotManager:
    output_filepath: Optional[str]
    memory_viz_args: Optional[list[str]]
    memory_viz_version: str = "latest"
    snapshot_counts = 0
    include: Optional[tuple[str, ...]]
    # TODO: do we want to let user hide specific variables, such as the manager itself?

    def __init__(
        self,
        memory_viz_args: Optional[list[str]] = None,
        output_filepath: Optional[str] = ".",
        include: Optional[tuple[str, ...]] = (".*",),
    ) -> None:
        if memory_viz_args is None:
            memory_viz_args = ["--roughjs-config", "seed=12345"]
        self.output_filepath = output_filepath
        self.memory_viz_args = memory_viz_args
        self.include = include

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        if event == "line" and frame.f_locals:
            # TODO: use snapshot(save=True)
            var_data = snapshot(include=self.include)
            json_data = snapshot_to_json(var_data)
            if json_data:
                self._output_snapshot(json_data)
                self.snapshot_counts += 1

    def get_snapshot_count(self):
        return self.snapshot_counts

    def __enter__(self):
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda frame, event, arg: None)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        sys.settrace(None)

    def _output_snapshot(self, data):
        command = ["npx", "memory-viz"]
        command.extend(self.memory_viz_args)
        command.extend(
            ["--output", os.path.join(self.output_filepath, f"snapshot-{self.snapshot_counts}.svg")]
        )
        npx_path = shutil.which("npx")
        subprocess.run(
            command,
            input=json.dumps(data),
            executable=npx_path,
            stdout=sys.stdout,
            stderr=sys.stderr,
            encoding="utf-8",
            text=True,
            check=True,
        )
