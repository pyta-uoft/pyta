"""
Tests for setendings.py, check `end_lineno` and `end_col_offset`
properties are set.
Run from /pyta/ dir: `python tests/test_setendings.py`
"""

import unittest
from astroid.node_classes import NodeNG
from python_ta.transforms.setendings import *
from colorama import Back, Fore

PATH = 'examples/ending_locations/'


class NodeNG(object):
    """Check `end_col_offset` and `end_lineno` properties are correctly set on
    the nodes. Use the node method `nodes_of_class`.
    https://github.com/PyCQA/astroid/blob/master/astroid/node_classes.py#L407
    """

    def __init__(self):
        super().__init__()
        self.reset()

    def reset(self):
        """Reset between test methods (and once on init).
        """
        # Keep a list rather than a set, because "too many" is wrong.
        self._props_check = []

    def check_endings(self, module, node_class):
        """Look at the nodes of a certain class, and inspect certain properties.
        """
        for node in module.nodes_of_class(node_class):  # generator
            try:
                self._props_check.append((node.fromlineno, node.end_lineno,
                                        node.col_offset, node.end_col_offset))
            except AttributeError:
                # raise again to also get traceback along with message.
                raise AttributeError('''Make sure the properties are set in
                    setendings.py and the function is registered
                    with ending_transformer.register_transform()''')
        return self._props_check


class TestEndingLocations(unittest.TestCase):
    """The method, ending_transformer.visit(module) walks the given astroid
    *tree* and transform each encountered node. Only the nodes which have
    transforms registered will actually be replaced or changed.

    We store the correct values as a tuple:
    (fromlineno, end_lineno, col_offset, end_col_offset)
    """

    @classmethod
    def setUpClass(self):
        """A class method called before tests in an individual class run.
        setUpClass is called with the class as the only argument and must be
        decorated as a classmethod():"""
        # Check the nodes property correctness.
        self.nodeng = NodeNG()
        self.maxDiff = None

    def setUp(self):
        """Method called to prepare the test fixture. This is called immediately
        before calling the test method; other than AssertionError or SkipTest,
        any exception raised by this method will be considered an error rather
        than a test failure. The default implementation does nothing."""
        pass

    def tearDown(self):
        """Method called immediately after the test method has been called and
        the result recorded. This is called even if the test method raised an
        exception, so the implementation in subclasses may need to be
        particularly careful about checking internal state. Any exception,
        other than AssertionError or SkipTest, raised by this method will be
        considered an additional error rather than a test failure (thus
        increasing the total number of reported errors). This method will only
        be called if the setUp() succeeds, regardless of the outcome of the
        test method. The default implementation does nothing."""
        self.nodeng.reset()

    def get_file_as_module(self, file_location):
        """Given a filepath (file_location), parse with astroid, and return
        the module.
        """
        with open(file_location) as f:
            content = f.read()
        return self.get_string_as_module(content)

    def get_string_as_module(self, string):
        """Parse the string with astroid, and return the module.

        Also initialize the ending transformer here.
        """
        source_lines = string.split('\n')
        # Instantiate a visitor, and register the transform functions to it.
        self.ending_transformer = init_register_ending_setters(source_lines)

        return astroid.parse(string)

    def set_and_check(self, module, node_class, expected):
        """Example is either in a file, or provided as a string literal.
        """
        self.ending_transformer.visit(module)  # Apply all transforms.
        props = self.nodeng.check_endings(module, node_class)  # Inspect parts.
        err_str = '\n{}\n'.format('- ' * 35)
        err_str += ' Compare: [(fromlineno, end_lineno, col_offset, end_col_offset)]\n'
        err_str += 'Expected: {}\n'.format(Fore.GREEN + str(expected) + Fore.RESET)
        err_str += '  Actual: {}'.format(Fore.RED + str(props) + Fore.RESET)
        self.assertEqual(expected, props, err_str)

    # def test_arguments(self):
    #     expected = [(1, 2, 8, 30), (5, 5, 14, 14), (8, 8, 12, 12), (9, 9, 14, 18)]
    #     module = self.get_file_as_module(PATH + 'arguments.py')
    #     self.set_and_check(module, astroid.Arguments, expected)

    def test_assert(self):
        expected = [(1, 1, 0, 43), (2, 2, 0, 11)]
        module = self.get_file_as_module(PATH + 'Assert.py')
        self.set_and_check(module, astroid.Assert, expected)

    def test_assign(self):
        expected = [(1, 1, 0, 5), (2, 2, 0, 9), (3, 3, 0, 11), (4, 4, 0, 8), (5, 5, 0, 6)]
        module = self.get_file_as_module(PATH + 'Assign.py')
        self.set_and_check(module, astroid.Assign, expected)

    def test_assignattr(self):
        """
        Given 'self.name = 10', we want to highlight 'self.name' rather than
        just 'self'.
        """
        expected = [(3, 3, 8, 17), (4, 4, 8, 19)]
        module = self.get_file_as_module(PATH + 'AssignAttr.py')
        self.set_and_check(module, astroid.AssignAttr, expected)

    # def test_assignname(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 5)]
    #     module = self.get_file_as_module(PATH + 'AssignName.py')
    #     self.set_and_check(module, astroid.Assign, expected)

    def test_asyncfor(self):
        """Note: col_offset property always set after the 'async' keyword.
        """
        expected = [(3, 7, 4, 16)]
        module = self.get_file_as_module(PATH + 'AsyncFor.py')
        self.set_and_check(module, astroid.AsyncFor, expected)

    # def test_asyncfunctiondef(self):
    #     """
    #     """
    #     expected = [(1, 2, 6, 12)]
    #     module = self.get_file_as_module(PATH + 'AsyncFunctionDef.py')
    #     self.set_and_check(module, astroid.AsyncFunctionDef, expected)

    # def test_asyncwith(self):
    #     """
    #     """
    #     expected = [(2, 3, 10, 12)]
    #     module = self.get_file_as_module(PATH + 'AsyncWith.py')
    #     self.set_and_check(module, astroid.AsyncWith, expected)

    def test_attribute(self):
        """Note: Setting the attribute node by its last child doesn't include
        the attribute in determining the end_col_offset.
        """
        expected = [(1, 1, 0, 12), (2, 2, 0, 14)]
        module = self.get_file_as_module(PATH + 'Attribute.py')
        self.set_and_check(module, astroid.Attribute, expected)

    # def test_augassign(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 6)]
    #     module = self.get_file_as_module(PATH + 'AugAssign.py')
    #     self.set_and_check(module, astroid.AugAssign, expected)

    # def test_await(self):
    #     """Note: col_offset property always set before the 'await' keyword.
    #     Aside: this example shows the case where setting end_col_offset by the
    #     child (i.e. arguments.Name) doesn't capture some information like the
    #     parenthesis in the parent arguments.Call node.
    #     """
    #     expected = [(5, 5, 4, 25)]
    #     module = self.get_file_as_module(PATH + 'Await.py')
    #     self.set_and_check(module, astroid.Await, expected)

    # def test_binop(self):
    #     """note: value of col_offset = 6, is weird but we didn't set it.
    #     first (depends on pre/postorder) binop is ((1 + 2) + 3), then (1 + 2)
    #     TODO: add the "( (100) * (42)  )" test
    #     """
    #     expected = [(1, 1, 6, 9), (1, 1, 0, 5)]
    #     example = '''1 + 2 + 3'''
    #     module = self.get_string_as_module(example)
    #     self.set_and_check(module, astroid.BinOp, expected)

    # def test_boolop(self):
    #     """
    #     """
    #     expected = [(1, 1, 4, 13)]
    #     module = self.get_file_as_module(PATH + 'BoolOp.py')
    #     self.set_and_check(module, astroid.BoolOp, expected)

    # def test_break(self):
    #     """
    #     """
    #     expected = [(2, 2, 4, 9)]
    #     module = self.get_file_as_module(PATH + 'Break.py')
    #     self.set_and_check(module, astroid.Break, expected)

    def test_call(self):
        """Note: the end_col_offset is 1 left of the last ')'.
        >>>print(1, 2, 3,
        >>>     4)
        """
        expected = [(1, 2, 0, 9)]
        module = self.get_file_as_module(PATH + 'Call.py')
        self.set_and_check(module, astroid.Call, expected)

    # def test_classdef(self):
    #     """Note: this is set to the last statement in the class definition.
    #     """
    #     expected = [(1, 2, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'ClassDef.py')
    #     self.set_and_check(module, astroid.ClassDef, expected)

    # def test_compare(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 5)]
    #     module = self.get_file_as_module(PATH + 'Compare.py')
    #     self.set_and_check(module, astroid.Compare, expected)

    def test_comprehension(self):
        """
        Could be in a SetComp, ListComp, or GeneratorExp.. in each respective
        case, the subsequent char could be either a brace, bracket, or paren.
        Aside: col_offset should start from beginning of the 'for'.
        """
        expected = [(1, 1, 7, 20), (2, 2, 7, 16), (2, 2, 21, 36), (3, 3, 9, 18), (3, 3, 23, 40)]
        module = self.get_file_as_module(PATH + 'Comprehension.py')
        self.set_and_check(module, astroid.Comprehension, expected)

    def test_const(self):
        """
        """
        expected = [(1, 1, 0, 6), (2, 2, 4, 6), (3, 3, 0, 3), (4, 4, 0, 8),
        (5, 7, 0, 1), (8, 8, 6, 11), (8, 8, 13, 25)]
        module = self.get_file_as_module(PATH + 'Const.py')
        self.set_and_check(module, astroid.Const, expected)

    def test_continue(self):
        """
        """
        expected = [(2, 2, 4, 12)]
        module = self.get_file_as_module(PATH + 'Continue.py')
        self.set_and_check(module, astroid.Continue, expected)

    def test_decorators(self):
        """
        Include the right parens (note: only if decorator takes args)
        """
        expected = [(1, 2, 0, 27), (6, 6, 0, 9)]
        module = self.get_file_as_module(PATH + 'Decorators.py')
        self.set_and_check(module, astroid.Decorators, expected)

    def test_delattr(self):
        """Include the 'del' keyword in the col_offset property.
        Include the attribute name in the end_col_offset property.
        """
        expected = [(4, 4, 8, 21), (5, 5, 8, 23)]
        module = self.get_file_as_module(PATH + 'DelAttr.py')
        self.set_and_check(module, astroid.DelAttr, expected)

    def test_delete(self):
        """Include the 'del' keyword in the col_offset property.
        """
        expected = [(1, 1, 0, 5), (2, 2, 0, 22)]
        module = self.get_file_as_module(PATH + 'Delete.py')
        self.set_and_check(module, astroid.Delete, expected)

    def test_delname(self):
        """Include the 'del' keyword in the col_offset property.
        """
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module(PATH + 'DelName.py')
        self.set_and_check(module, astroid.DelName, expected)

    def test_dict(self):
        expected = [(1, 1, 6, 32), (2, 5, 4, 1), (6, 9, 4, 6)]
        module = self.get_file_as_module(PATH + 'Dict.py')
        self.set_and_check(module, astroid.Dict, expected)

    def test_dictcomp(self):
        """Buggy
        """
        expected = [(1, 1, 0, 29), (2, 2, 0, 37), (3, 7, 0, 1)]
        module = self.get_file_as_module(PATH + 'DictComp.py')
        self.set_and_check(module, astroid.DictComp, expected)

    # def test_dictunpack(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module(PATH + 'DictUnpack.py')
    #     self.set_and_check(module, astroid.DictUnpack, expected)

    # def test_ellipsis(self):
    #     expected = [(1, 1, 0, 3)]
    #     module = self.get_file_as_module(PATH + 'Ellipsis.py')
    #     self.set_and_check(module, astroid.Ellipsis, expected)

    # def test_emptynode(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module(PATH + 'EmptyNode.py')
    #     self.set_and_check(module, astroid.EmptyNode, expected)

    # def test_excepthandler(self):
    #     expected = [(3, 4, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'ExceptHandler.py')
    #     self.set_and_check(module, astroid.ExceptHandler, expected)

    # def test_exec(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module(PATH + 'Exec.py')
    #     self.set_and_check(module, astroid.Exec, expected)

    # def test_expr(self):
    #     """TODO: test all the Expr nodes in 'Slice.py'
    #     """
    #     expected = [(1, 1, 0, 12), (2, 2, 0, 13), (3, 3, 0, 11), (4, 4, 0, 17)]
    #     module = self.get_file_as_module(PATH + 'Expr.py')
    #     self.set_and_check(module, astroid.Expr, expected)

    def test_extslice(self):
        """
        """
        expected = [(1, 1, 1, 8), (2, 2, 2, 14), (3, 3, 1, 8), (4, 4, 2, 15), (5, 6, 1, 8)]
        module = self.get_file_as_module(PATH + 'ExtSlice.py')
        self.set_and_check(module, astroid.ExtSlice, expected)

    # def test_for(self):
    #     expected = [(1, 2, 0, 9)]
    #     module = self.get_file_as_module(PATH + 'For.py')
    #     self.set_and_check(module, astroid.For, expected)

    # def test_functiondef(self):
    #     expected = [(1, 2, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'FunctionDef.py')
    #     self.set_and_check(module, astroid.FunctionDef, expected)

    def test_generatorexp(self):
        expected = [(1, 1, 0, 37), (2, 2, 0, 43)]
        module = self.get_file_as_module(PATH + 'GeneratorExp.py')
        self.set_and_check(module, astroid.GeneratorExp, expected)

    # def test_global(self):
    #     """
    #     """
    #     expected = [(2, 2, 4, 12)]
    #     module = self.get_file_as_module(PATH + 'Global.py')
    #     self.set_and_check(module, astroid.Global, expected)

    # def test_if(self):
    #     """
    #     """
    #     expected = [(1, 4, 0, 8), (3, 4, 5, 8)]
    #     module = self.get_file_as_module(PATH + 'If.py')
    #     self.set_and_check(module, astroid.If, expected)

    # def test_ifexp(self):
    #     """
    #     """
    #     expected = [(1, 1, 4, 20)]
    #     module = self.get_file_as_module(PATH + 'IfExp.py')
    #     self.set_and_check(module, astroid.IfExp, expected)

    # def test_import(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 14)]
    #     module = self.get_file_as_module(PATH + 'Import.py')
    #     self.set_and_check(module, astroid.Import, expected)

    # def test_importfrom(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 47)]
    #     module = self.get_file_as_module(PATH + 'ImportFrom.py')
    #     self.set_and_check(module, astroid.ImportFrom, expected)

    def test_index(self):
        """Should include the enclosing brackets, e.g. "[1]" instead of "1".
        """
        expected = [(1, 1, 1, 5), (2, 2, 2, 10), (3, 3, 2, 15)]
        module = self.get_file_as_module(PATH + 'Index.py')
        self.set_and_check(module, astroid.Index, expected)

    def test_keyword(self):
        """Include the name of the keyword, contained in 'node.arg' attribute.
        """
        expected = [(1, 1, 4, 12), (2, 2, 5, 15)]
        module = self.get_file_as_module(PATH + 'Keyword.py')
        self.set_and_check(module, astroid.Keyword, expected)

    # def test_lambda(self):
    #     """
    #     """
    #     expected = [(1, 1, 6, 15), (2, 2, 7, 25)]
    #     module = self.get_file_as_module(PATH + 'Lambda.py')
    #     self.set_and_check(module, astroid.Lambda, expected)

    # def test_list(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 2)]
    #     module = self.get_file_as_module(PATH + 'List.py')
    #     self.set_and_check(module, astroid.List, expected)

    # def test_listcomp(self):
    #     """Buggy
    #     """
    #     expected = [(1, 1, 0, 24), (2, 2, 0, 49)]
    #     module = self.get_file_as_module(PATH + 'ListComp.py')
    #     self.set_and_check(module, astroid.ListComp, expected)

    # def test_module(self):
    #     """
    #     """
    #     expected = [(0, 2, 0, 1)]
    #     module = self.get_file_as_module(PATH + 'Module.py')
    #     self.set_and_check(module, astroid.Module, expected)

    # def test_name(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 6)]
    #     module = self.get_file_as_module(PATH + 'Name.py')
    #     self.set_and_check(module, astroid.Name, expected)

    # def test_nonlocal(self):
    #     """
    #     """
    #     expected = [(3, 3, 4, 14)]
    #     module = self.get_file_as_module(PATH + 'Nonlocal.py')
    #     self.set_and_check(module, astroid.Nonlocal, expected)

    # def test_pass(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 4)]
    #     module = self.get_file_as_module(PATH + 'Pass.py')
    #     self.set_and_check(module, astroid.Pass, expected)

    # def test_print(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module(PATH + 'Print.py')
    #     self.set_and_check(module, astroid.Print, expected)

    # def test_raise(self):
    #     expected = [(1, 1, 0, 23)]
    #     module = self.get_file_as_module(PATH + 'Raise.py')
    #     self.set_and_check(module, astroid.Raise, expected)

    # def test_repr(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module(PATH + 'Repr.py')
    #     self.set_and_check(module, astroid.Repr, expected)

    # def test_return(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'Return.py')
    #     self.set_and_check(module, astroid.Return, expected)

    def test_set(self):
        expected = [(1, 1, 0, 3), (2, 2, 0, 6), (3, 3, 0, 12)]
        module = self.get_file_as_module(PATH + 'Set.py')
        self.set_and_check(module, astroid.Set, expected)

    def test_setcomp(self):
        expected = [(1, 1, 0, 25), (2, 2, 0, 63)]
        module = self.get_file_as_module(PATH + 'SetComp.py')
        self.set_and_check(module, astroid.SetComp, expected)

    def test_slice(self):
        """Note: col_offset and end_col_offset are set to the first constant
        encountered, either on left or right side of colon.
        Should capture both brackets..
        """
        expected = [(1, 1, 2, 3),
                    (2, 2, 3, 8),
                    (3, 3, 2, 4),
                    (4, 4, 3, 13),
                    (5, 5, 2, 8),
                    (6, 6, 8, 30),
                    (7, 8, 2, 2),
                    (9, 9, 2, 4),
                    (9, 9, 6, 7),
                    (10, 10, 2, 3),
                    (10, 10, 5, 7),
                    (11, 11, 2, 3),
                    (11, 11, 5, 6),
                    (12, 12, 2, 4),
                    (13, 13, 2, 3),
                    (13, 13, 10, 11),
                    (14, 14, 6, 11),
                    (15, 15, 2, 3),
                    (15, 15, 5, 6),
                    (15, 15, 9, 10)
                    ]
        module = self.get_file_as_module(PATH + 'Slice.py')
        self.set_and_check(module, astroid.Slice, expected)

    # def test_starred(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 2)]
    #     module = self.get_file_as_module(PATH + 'Starred.py')
    #     self.set_and_check(module, astroid.Starred, expected)

    def test_subscript(self):
        """
        """
        expected = [(1, 1, 0, 4),
                    (2, 2, 0, 8),
                    (3, 3, 0, 4),
                    (4, 4, 0, 9),
                    (5, 5, 0, 5),
                    (6, 6, 0, 14),
                    (7, 7, 0, 9),
                    (8, 8, 4, 31),
                    (9, 10, 0, 3),
                    (11, 11, 0, 8),
                    (11, 11, 0, 5),
                    (12, 12, 0, 8),
                    (12, 12, 0, 4),
                    (13, 13, 0, 7),
                    (13, 13, 0, 4),
                    (14, 14, 0, 5),
                    (15, 15, 0, 12),
                    (15, 15, 0, 4),
                    (16, 16, 4, 12)
                    ]
        module = self.get_file_as_module(PATH + 'Subscript.py')
        self.set_and_check(module, astroid.Subscript, expected)

    # def test_tryexcept(self):
    #     """
    #     """
    #     expected = [(1, 4, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'TryExcept.py')
    #     self.set_and_check(module, astroid.TryExcept, expected)

    # def test_tryfinally(self):
    #     """
    #     """
    #     expected = [(1, 6, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'TryFinally.py')
    #     self.set_and_check(module, astroid.TryFinally, expected)

    def test_tuple(self):
        expected = [(1, 1, 0, 6), (2, 2, 0, 11), (3, 3, 0, 5), (4, 4, 0, 7),
                    (5, 5, 0, 12), (6, 8, 0, 8), (9, 9, 0, 4), (10, 10, 0, 7),
                    (11, 13, 0, 17)
                    ]
        module = self.get_file_as_module(PATH + 'Tuple.py')
        self.set_and_check(module, astroid.Tuple, expected)

    # def test_unaryop(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'UnaryOp.py')
    #     self.set_and_check(module, astroid.UnaryOp, expected)

    # def test_while(self):
    #     """
    #     """
    #     expected = [(1, 2, 0, 9)]
    #     module = self.get_file_as_module(PATH + 'While.py')
    #     self.set_and_check(module, astroid.While, expected)

    # def test_with(self):
    #     """
    #     """
    #     expected = [(1, 2, 0, 8)]
    #     module = self.get_file_as_module(PATH + 'With.py')
    #     self.set_and_check(module, astroid.With, expected)

    # def test_yield(self):
    #     """
    #     """
    #     expected = [(1, 1, 0, 5)]
    #     module = self.get_file_as_module(PATH + 'Yield.py')
    #     self.set_and_check(module, astroid.Yield, expected)

    # def test_yieldfrom(self):
    #     """
    #     """
    #     expected = [(2, 2, 4, 16)]
    #     module = self.get_file_as_module(PATH + 'YieldFrom.py')
    #     self.set_and_check(module, astroid.YieldFrom, expected)


if __name__ == '__main__':
    unittest.main()  # run tests
