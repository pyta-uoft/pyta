from docstring.csc108_docstring import *
import unittest


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


class DocstringParserTest(unittest.TestCase):
    def test_simple_docstring(self):
        dsp = DocstringParser('(int) -> bool')
        self.assertEqual(1, len(dsp.args_node.children))
        self.assertEqual('int', dsp.args_node.children[0].node_type)
        self.assertEqual(1, len(dsp.return_node.children))
        self.assertEqual('bool', dsp.return_node.children[0].node_type)

    def test_empty_docstring(self):
        dsp = DocstringParser('() -> NoneType')
        self.assertEqual(0, len(dsp.args_node.children))
        self.assertEqual(1, len(dsp.return_node.children))
        self.assertEqual('NoneType', dsp.return_node.children[0].node_type)

    def test_multi_arg_docstring(self):
        dsp = DocstringParser('(int, str) -> NoneType')
        self.assertEqual(2, len(dsp.args_node.children))
        self.assertEqual('int', dsp.args_node.children[0].node_type)
        self.assertEqual('str', dsp.args_node.children[1].node_type)
        self.assertEqual(1, len(dsp.return_node.children))
        self.assertEqual('NoneType', dsp.return_node.children[0].node_type)

    def test_list_docstring(self):
        dsp = DocstringParser('(set of bool) -> list of int')
        self.assertEqual(1, len(dsp.args_node.children))
        child = dsp.args_node.children[0]
        self.assertEqual('set', child.node_type)
        self.assertEqual(1, len(child.children))
        self.assertEqual('bool', child.children[0].node_type)
        self.assertEqual(1, len(dsp.return_node.children))
        child = dsp.return_node.children[0]
        self.assertEqual('list', child.node_type)
        self.assertEqual(1, len(child.children))
        self.assertEqual('int', child.children[0].node_type)

    def test_dict_tuple_docstring(self):
        dsp = DocstringParser('(dict of {int, str}) -> tuple of (int, float, int)')
        self.assertEqual(1, len(dsp.args_node.children))
        child = dsp.args_node.children[0]
        self.assertEqual('dict', child.node_type)
        self.assertEqual(2, len(child.children))
        self.assertEqual('int', child.children[0].node_type)
        self.assertEqual('str', child.children[1].node_type)
        self.assertEqual(1, len(dsp.return_node.children))
        child = dsp.return_node.children[0]
        self.assertEqual('tuple', child.node_type)
        self.assertEqual(3, len(child.children))
        self.assertEqual('int', child.children[0].node_type)
        self.assertEqual('float', child.children[1].node_type)
        self.assertEqual('int', child.children[2].node_type)

    def test_nested_collections(self):
        dsp = DocstringParser('(list of dict of {int, str}) -> int')
        self.assertEqual(1, len(dsp.args_node.children))
        child = dsp.args_node.children[0]
        self.assertEqual('list', child.node_type)
        child = child.children[0]
        self.assertEqual(2, len(child.children))
        self.assertEqual('int', child.children[0].node_type)
        self.assertEqual('str', child.children[1].node_type)
        self.assertEqual(1, len(dsp.return_node.children))
        self.assertEqual('int', dsp.return_node.children[0].node_type)

    def test_malformed_docstring_no_end(self):
        try:
            DocstringParser('() -> ')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_missing_of(self):
        try:
            DocstringParser('(list int) -> int')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_extra_basetype(self):
        try:
            DocstringParser('(int, str bool) -> bool')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_premature_termination(self):
        try:
            DocstringParser('(int, str')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_missing_arrow(self):
        try:
            DocstringParser('(int, str bool) -> int')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_bad_dict(self):
        try:
            DocstringParser('(dict of {int}) -> bool')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_empty_tuple(self):
        try:
            DocstringParser('(tuple of ()) -> bool')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_tuple_missing_arg(self):
        try:
            DocstringParser('(tuple of (int, str, )) -> bool')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_multi_return_args(self):
        try:
            DocstringParser('(int) -> bool, int')
            self.fail()
        except NotA108DocstringException:
            pass

    def test_malformed_docstring_empty_string(self):
        try:
            DocstringParser('')
            self.fail()
        except NotA108DocstringException:
            pass


if __name__ == '__main__':
    unittest.main()
