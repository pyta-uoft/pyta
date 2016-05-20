"""pylint: redundant unittest assert
"""

import unittest

class TestStringMethods(unittest.TestCase):
    """Simple tests for example purposes."""

    def test_isupper(self):
        """Simple tests for example purposes."""

        # Valid:
        self.assertTrue('FOO'.isupper())
        self.assertFalse('bar'.isupper())

        # If a constant is passed as parameter, that condition is always true:
        self.assertTrue('YES')
        self.assertTrue(1)
        self.assertTrue(True)
        self.assertTrue(False)
