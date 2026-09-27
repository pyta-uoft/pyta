"""
This Python module is designed for testing the snapshot function's ability to, when save is True
and npx cannot be found on the PATH, raise an informative error instead of creating a subprocess.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

from python_ta.debug.snapshot import snapshot

test_var1a = "Allyssa was here :)"
test_var2a = "Students Developing Software"
snapshot(True)
