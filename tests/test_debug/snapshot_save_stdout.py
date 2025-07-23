"""
This Python module is designed for testing the snapshot function's ability to, when save is True,
return the snapshot svg to stdout.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

from python_ta.debug.id_tracker import IDTracker
from python_ta.debug.snapshot import snapshot

test_var1a = "David is cool!"
test_var2a = "Students Developing Software"
snapshot(IDTracker(), True, ["--roughjs-config", "seed=12345"], "0.3.1")
