"""
This Python module is designed for testing the snapshot function's ability to stop at the
outermost <module> stack frame of exec'd code, without "breaking out of" the exec call.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

from python_ta.debug.snapshot import snapshot

outer_global = "should not be captured"

EXEC_CODE = """
import json

exec_global = 2

def exec_func():
    exec_var = 1
    return snapshot()

print(json.dumps(exec_func()))
"""


def outer_func() -> None:
    """Call exec on EXEC_CODE from within a function."""
    outer_local = "should not be captured"
    exec(EXEC_CODE, {"snapshot": snapshot})


outer_func()
