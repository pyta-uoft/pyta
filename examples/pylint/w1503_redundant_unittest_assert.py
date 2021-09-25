from typing import List
import unittest

def is_sorted(lst: List[float]) -> bool:
    """Check if <lst> is sorted in ascending order."""
    return lst == sorted(lst)


class TestStringMethods(unittest.TestCase):
    """Simple tests for example purposes."""

    def test_isupper(self) -> None:
        """Simple tests for example purposes."""
        # Valid:
        self.assertTrue(is_sorted([1, 2, 3]))
        self.assertFalse(is_sorted([1, 3, 2]))

        # If a constant is passed as parameter, that condition is always true:
        self.assertTrue('YES')
        self.assertTrue(1)
        self.assertTrue(True)
        self.assertTrue(False)
