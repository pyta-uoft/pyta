"""Run our check on a number of different nodes.
Currently doesn't work to run on a top level directory like 
`python_ta.check_all('nodes')` so instead we iterate over the
files in a directory, using the dot notation that check expects,
like `python_ta.check_all('nodes.assert')`.
"""
import unittest
import os
import sys

# add dir, /pyta/ to sys path to find local copy of python_ta package first, 
# rather than using the installed python_ta.
sys.path.insert(0, os.path.abspath(os.path.join(os.getcwd(), os.pardir)))
import python_ta

_RELATIVE = '../'
_NODES_PATH_TOP_LEVEL = 'nodes'


def get_file_paths(rel_path):
    """A generator for python files within a directory.
    `rel_path` is a relative path. Returns a path in dot notation.
    """
    test_files = []
    for root, _, files in os.walk(rel_path):
        for filename in (f for f in files if f.endswith('.py')):
            # Format path, starts at root package
            yield root.replace(_RELATIVE, '', 1) + '.' + filename.replace('.py', '')
    return test_files

class TestCheck(unittest.TestCase):
    def test_check(self):
        """Note: the argument to check_all() should use dot notation."""
        for test_file in get_file_paths(_RELATIVE + _NODES_PATH_TOP_LEVEL):
            try:
                python_ta.check_all(test_file)
            except Exception as exc:
                ass_msg = 'Exception raised when checking file: ' \
                          '"{}".\n{}'.format(test_file, exc)
                self.fail(ass_msg)

if __name__ == '__main__':
    unittest.main()  # run tests
