"""Unittest for the pyparser."""

import unittest
from typing import *
from python_ta.parser.pyparser import *


class TypeTest(unittest.TestCase):
    """testers specifically for the function set_const using single nodes."""
    def test_1(self):
        """testing 3//= 3."""
        result = parse(tokenize('3 //= 3'))
        self.assertEqual(1, result)

    def test_2(self):
        """testing 3 += 3."""
        result = parse(tokenize('3 += 3'))
        self.assertEqual(6, result)

    def test_3(self):
        """testing (3 - 3) * 3 + (3 * 3)."""
        result = parse(tokenize('(3 - 3) * 3 + (3 * 3)'))
        self.assertEqual(9, result)

    def test_4(self):
        """testing (3 - 1) * 3) + (3 * 3)"""
        result = parse(tokenize('((3 - 1) * 3) + (3 * 3)'))
        self.assertEqual(15, result)

    def test_5(self):
        """testing 2 * 32 ** 1 == 64"""
        result = parse(tokenize('2 * 32 ** 1')) == 64
        self.assertEqual(True, result)
        
    def test_6(self):
        """testing 2 ** 32 - 1 == 4294967295"""
        result = parse(tokenize('2 ** 32 - 1')) == 4294967295
        self.assertEqual(True, result)
        
    def test_7(self):
        """testing 2 // 3 - 1"""
        result = parse(tokenize('2 // 3 - 1'))
        self.assertEqual(-1, result)
        
if __name__ == "__main__":
    unittest.main()