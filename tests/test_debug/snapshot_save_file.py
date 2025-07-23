"""
This Python module is designed for testing the snapshot function's ability to, when save is True,
create a snapshot svg at the specified file path.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

import os
import sys

from python_ta.debug.id_tracker import IDTracker
from python_ta.debug.snapshot import snapshot

test_var1a = "David is cool!"
test_var2a = "Students Developing Software"
snapshot(
    IDTracker(),
    True,
    [
        "--output=" + os.path.abspath(sys.argv[1]),
        "--roughjs-config",
        "seed=12345",
    ],
    "0.3.1",
)
