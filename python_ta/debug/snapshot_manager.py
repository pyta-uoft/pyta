import inspect
import json
import shutil
import subprocess
import sys
import types
from typing import Any, List, Optional

from build.lib.python_ta.debug.snapshot import snapshot_to_json
from python_ta.debug.snapshot import snapshot


class SnapshotManager:
    output_filepath: Optional[str]
    # TODO: json or jsons?
    snapshot_jsons: List[List[dict]]
    curr_line: int

    def __init__(self, output_filepath: Optional[str] = ".") -> None:
        self.output_filepath = output_filepath
        self.snapshot_jsons = []
        self.curr_line = 1

    def _trace_func(self, _: types.FrameType, event: str, _arg: Any) -> None:
        if event == "line":
            # TODO: the snapshot returns everything in the call stack above, so hard coding
            # to only look at the second frame probably won't work
            var_data = [snapshot()[1]]
            json_data = snapshot_to_json(var_data)
            self.snapshot_jsons.append(json_data)

    def __enter__(self) -> None:
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        func_frame.f_trace = self._trace_func
        sys.settrace(lambda frame, event, arg: None)

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        sys.settrace(None)
        command = ["npx", "memory-viz"]
        npx_path = shutil.which("npx")
        for i, snapshot_json in enumerate(self.snapshot_jsons):
            command.extend(["--output", f"snapshot-{i}.svg"])
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
