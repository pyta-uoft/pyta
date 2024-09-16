import inspect
import json
import os
import shutil
import subprocess
import sys
import types
from typing import Any, List, Optional

from python_ta.debug.snapshot import snapshot, snapshot_to_json


class SnapshotManager:
    output_filepath: Optional[str]
    snapshots: List[List[dict]]

    def __init__(self, output_filepath: Optional[str] = ".") -> None:
        self.output_filepath = output_filepath
        self.snapshots = []

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        if event == "line" and frame.f_locals:
            # TODO: the snapshot returns everything in the call stack above, so hard coding \
            #  to only look at the second frame probably won't work
            var_data = [snapshot()[1]]
            json_data = snapshot_to_json(var_data)
            self.snapshots.append(json_data)

    def get_snapshot_count(self):
        return len(self.snapshots)

    def __enter__(self):
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda frame, event, arg: None)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        sys.settrace(None)
        # TODO: to produce consistent svgs for testing, we use a fixed seed. We can set this as \
        #  a default option
        command = ["npx", "memory-viz", "--roughjs-config", "seed=12345"]
        npx_path = shutil.which("npx")
        for i, snapshot_json in enumerate(self.snapshots):
            command.extend(["--output", os.path.join(self.output_filepath, f"snapshot-{i}.svg")])
            subprocess.run(
                command,
                input=json.dumps(snapshot_json),
                executable=npx_path,
                stdout=sys.stdout,
                stderr=sys.stderr,
                encoding="utf-8",
                text=True,
                check=True,
            )
