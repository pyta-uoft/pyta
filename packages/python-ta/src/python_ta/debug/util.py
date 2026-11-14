"""Helper functions shared by the python_ta.debug modules."""

from __future__ import annotations

import os
import sys
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from types import CodeType


def exec_as_main(code: CodeType, path: str, extra_globals: dict[str, Any]) -> None:
    """Run the given code as the "__main__" module of the Python file at path, as running
    the file directly with Python would.

    Args:
        code: The compiled code of the file.
        path: The path to the Python file the code was compiled from.
        extra_globals: Additional global variables to define before running the code.
    """
    # Add the file's directory to the import path, as running it directly would
    old_path = sys.path[:]
    sys.path.insert(0, os.path.dirname(os.path.abspath(path)))
    try:
        exec(code, {"__name__": "__main__", "__file__": path, **extra_globals})
    finally:
        sys.path[:] = old_path
