"""
This Python module is designed for testing the run_with_snapshots function's ability to run
a file containing snapshot comments, given as the first command-line argument.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

import sys

from python_ta.debug.snapshot import run_with_snapshots

run_with_snapshots(sys.argv[1])
