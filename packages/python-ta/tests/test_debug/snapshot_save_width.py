"""
This Python module is designed for testing the snapshot function's ability to, when save is True,
return the snapshot svg to stdout with the width specified in memory_viz_args.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

from python_ta.debug.snapshot import snapshot

test_var1a = "David is cool!"
test_var2a = "Students Developing Software"
snapshot(True, ["--width", "1200", "--roughjs-config", "seed=12345"], "0.3.1")
