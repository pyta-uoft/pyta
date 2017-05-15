"""Run always from the `pyta` root directory, so the local `python_ta` is
used rather than the installed `python_ta` package.
"""
import unittest
import os
import sys
import python_ta

_NODES_PATH_TOP_LEVEL = 'nodes'


class TestCheck(unittest.TestCase):
    def test_check_on_nodes_dir(self):
        """Note: the argument to check_all() should handle a top-level dir."""
        try:
            python_ta.check_all(_NODES_PATH_TOP_LEVEL)
        except Exception as exc:
            ass_msg = 'Exception raised when checking: ' \
                      '"{}".\n{}'.format(_NODES_PATH_TOP_LEVEL, exc)
            self.fail(ass_msg)
        

if __name__ == '__main__':
    unittest.main()  # run tests
