"""pylint: redundant unittest assert

The first argument of assertTrue and assertFalse is a "condition", which should
evaluate to True or False. If the condition is a constant value, then it is
considered to always be True, since it cannot be anything different.

The warning message looks like:
Redundant use of (assertTrue or assertFalse) with constant value <your-constant>

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
        self.assertTrue(False)  # even this!
