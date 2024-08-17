"""
This Python module is designed for testing the snapshot function's ability to, when save is True,
create a snapshot svg at the specified file path.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

import os

from python_ta.debug.snapshot import snapshot

test_var1a = "David is cool!"
test_var2a = "Students Developing Software"
snapshot(
    True,
    [
        "--output="
        + os.path.join(os.path.dirname(os.path.abspath(__file__)), "snapshot_testing_snapshots"),
        "--roughjs-config",
        "seed=12345",
    ],
    "0.3.1",
)
