import unittest
from docstring.csc108_docstring import *


class CSC108DocstringTest(unittest.TestCase):
    def test_docstring_parse_simple(self):
        docstr = '(int) -> str'
        self.assertEqual(docstr, trim_docstring_down_to_type_contract(docstr))

    def test_docstring_parse_doubleline(self):
        docstr = '''(int, int, int)
                     -> list of int'''
        result = trim_docstring_down_to_type_contract(docstr)
        expected = '(int, int, int) -> list of int'
        self.assertEqual(expected, result)

    def test_docstring_parse_multiline(self):
        docstr = '''(int, int, int)
                     ->\nlist of int'''
        result = trim_docstring_down_to_type_contract(docstr)
        expected = '(int, int, int) -> list of int'
        self.assertEqual(expected, result)

    def test_tokenize_docstring_simple(self):
        tokens = tokenize_docstring('(int, list of str) -> bool')
        self.assertEqual(['(', 'int', ',', 'list', 'of', 'str', ')', '->', 'bool'], tokens)

    def test_tokenize_docstring_complex(self):
        docstr = 'list of tuple of (int, MyClass, dict of {int, str})   -> list of list of int'
        tokens = tokenize_docstring(docstr)
        expected = ['list', 'of', 'tuple', 'of', '(', 'int', ',', 'MyClass', ',', 'dict', 'of',
                    '{', 'int', ',', 'str', '}', ')', '->', 'list', 'of', 'list', 'of', 'int']
        self.assertEqual(tokens, expected)

    def test_tokenize_docstring_malformed(self):
        try:
            tokenize_docstring('(int +) -> bool')
            self.fail()  # TODO - is there a better way? Like an expected exception decorator?
        except UnexpectedToken:
            pass


if __name__ == '__main__':
    unittest.main()
