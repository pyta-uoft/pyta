"""Run always from the `pyta` root directory, so the local `python_ta` is
used rather than the installed `python_ta` package.
"""
import os
import sys
import python_ta

_NODES_PATH_TOP_LEVEL = 'nodes'


def test_check_on_nodes_dir():
    """Note: the argument to check_all() should handle a top-level dir."""
    python_ta.check_all(_NODES_PATH_TOP_LEVEL)
