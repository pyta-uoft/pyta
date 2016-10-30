"""
Tests for setendings.py, check `end_lineno` and `end_col_offset`
properties are set.
To run: python tests/test_setendings.py
"""

import unittest
from astroid.bases import NodeNG
from python_ta.transforms.setendings import *


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


class TestEndingLocation(unittest.TestCase):
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

    def _assertSameness(self, expected, props):
        """If sequences are not equal, it is convenient to see each side, and
        any other info you want to print.
        """
        try:
            self.assertEqual(expected, props)
        except AssertionError as e:
            print('\n{}'.format('-'*70))
            print(' Compare: [(fromlineno, end_lineno, col_offset, end_col_offset)]')
            print('Expected: {}'.format(expected))
            print('  Actual: {}'.format(props))
            print('{}'.format('-'*70))
            raise e  # otherwise, test will always 'pass'

    def set_and_check(self, module, node_class, expected):
        """Example is either in a file, or provided as a string literal.
        """
        self.ending_transformer.visit(module)
        props = self.nodeng.check_endings(module, node_class)
        self._assertSameness(expected, props)

    def test_arguments(self):
        expected = [(1, 2, 8, 30), (5, 5, 14, 14), (8, 8, 12, 12), (9, 9, 14, 18)]
        module = self.get_file_as_module('examples/ending_locations/arguments.py')
        self.set_and_check(module, astroid.Arguments, expected)

    def test_assert(self):
        expected = [(1, 1, 0, 43), (2, 2, 0, 11)]
        module = self.get_file_as_module('examples/ending_locations/assert.py')
        self.set_and_check(module, astroid.Assert, expected)

    def test_assign(self):
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module('nodes/Assign.py')
        self.set_and_check(module, astroid.Assign, expected)

    def test_assignattr(self):
        expected = [(3, 3, 8, 12)]
        module = self.get_file_as_module('nodes/AssignAttr.py')
        self.set_and_check(module, astroid.AssignAttr, expected)

    def test_assignname(self):
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module('nodes/AssignName.py')
        self.set_and_check(module, astroid.Assign, expected)

    def test_asyncfor(self):
        """Note: col_offset property always set after the 'async' keyword.
        """
        expected = [(3, 4, 10, 12)]
        module = self.get_file_as_module('nodes/AsyncFor.py')
        self.set_and_check(module, astroid.AsyncFor, expected)

    def test_asyncfunctiondef(self):
        expected = [(1, 2, 6, 12)]
        module = self.get_file_as_module('nodes/AsyncFunctionDef.py')
        self.set_and_check(module, astroid.AsyncFunctionDef, expected)

    def test_asyncwith(self):
        expected = [(2, 3, 10, 12)]
        module = self.get_file_as_module('nodes/AsyncWith.py')
        self.set_and_check(module, astroid.AsyncWith, expected)

    def test_attribute(self):
        """Note: Setting the attribute node by its last child doesn't include
        the attribute in determining the end_col_offset.
        """
        expected = [(1, 1, 0, 7), (2, 2, 0, 8)]
        module = self.get_file_as_module('nodes/Attribute.py')
        self.set_and_check(module, astroid.Attribute, expected)

    def test_augassign(self):
        expected = [(1, 1, 0, 6)]
        module = self.get_file_as_module('nodes/AugAssign.py')
        self.set_and_check(module, astroid.AugAssign, expected)

    def test_await(self):
        """Note: col_offset property always set before the 'await' keyword.
        Aside: this example shows the case where setting end_col_offset by the
        child (i.e. arguments.Name) doesn't capture some information like the
        parenthesis in the parent arguments.Call node.
        """
        expected = [(5, 5, 4, 25)]
        module = self.get_file_as_module('nodes/Await.py')
        self.set_and_check(module, astroid.Await, expected)

    def test_binop(self):
        """note: value of col_offset = 6, is weird but we didn't set it.
        first (depends on pre/postorder) binop is ((1 + 2) + 3), then (1 + 2)
        """
        expected = [(1, 1, 6, 9), (1, 1, 0, 5)]
        example = '''1 + 2 + 3'''
        module = self.get_string_as_module(example)
        self.set_and_check(module, astroid.BinOp, expected)

    def test_boolop(self):
        expected = [(1, 1, 4, 13)]
        module = self.get_file_as_module('nodes/BoolOp.py')
        self.set_and_check(module, astroid.BoolOp, expected)

    def test_break(self):
        expected = [(2, 2, 4, 9)]
        module = self.get_file_as_module('nodes/Break.py')
        self.set_and_check(module, astroid.Break, expected)

    def test_call(self):
        """Note: the end_col_offset is 1 left of the last ')'.
        """
        expected = [(1, 1, 0, 7)]
        module = self.get_file_as_module('nodes/Call.py')
        self.set_and_check(module, astroid.Call, expected)

    def test_classdef(self):
        """Note: this is set to the last statement in the class definition.
        """
        expected = [(1, 2, 0, 8)]
        module = self.get_file_as_module('nodes/ClassDef.py')
        self.set_and_check(module, astroid.ClassDef, expected)

    def test_compare(self):
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module('nodes/Compare.py')
        self.set_and_check(module, astroid.Compare, expected)

    def test_comprehension(self):
        """Note: The end_col_offset is currently being set by the node
        astroid.AssignName, which may not be desired.
        """
        expected = [(1, 1, 7, 20)]
        module = self.get_file_as_module('nodes/Comprehension.py')
        self.set_and_check(module, astroid.Comprehension, expected)

    def test_const(self):
        expected = [(1, 1, 0, 6), (2, 2, 4, 6)]
        module = self.get_file_as_module('examples/ending_locations/const.py')
        self.set_and_check(module, astroid.Const, expected)

    def test_continue(self):
        expected = [(2, 2, 4, 12)]
        module = self.get_file_as_module('nodes/Continue.py')
        self.set_and_check(module, astroid.Continue, expected)

    def test_decorators(self):
        expected = [(1, 1, 0, 16)]
        module = self.get_file_as_module('nodes/Decorators.py')
        self.set_and_check(module, astroid.Decorators, expected)

    def test_delattr(self):
        """Note: col_offset property is set _after_ the 'del' keyword, and the
        attribute is not included in the end_col_offset.
        """
        expected = [(4, 4, 12, 16)]
        module = self.get_file_as_module('nodes/DelAttr.py')
        self.set_and_check(module, astroid.DelAttr, expected)

    def test_delete(self):
        """Note: col_offset property is set _before_ the 'del' keyword.
        """
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module('nodes/Delete.py')
        self.set_and_check(module, astroid.Delete, expected)

    def test_delname(self):
        """Note: col_offset property is set on the next node _after_ the 'del'
        keyword.
        """
        expected = [(1, 1, 4, 5)]
        module = self.get_file_as_module('nodes/DelName.py')
        self.set_and_check(module, astroid.DelName, expected)

    def test_dict(self):
        expected = [(1, 3, 4, 10)]
        module = self.get_file_as_module('examples/ending_locations/dict.py')
        self.set_and_check(module, astroid.Dict, expected)

    def test_dictcomp(self):
        """Note: col_offset is before first '{' (i.e. astroid.DictComp node),
        end_col_offset is after the '3' (i.e. astroid.Const last child node).
        """
        expected = [(1, 1, 0, 28)]
        module = self.get_file_as_module('nodes/DictComp.py')
        self.set_and_check(module, astroid.DictComp, expected)

    # def test_dictunpack(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('nodes/DictUnpack.py')
    #     self.set_and_check(module, astroid.DictUnpack, expected)

    def test_ellipsis(self):
        expected = [(1, 1, 0, 3)]
        module = self.get_file_as_module('nodes/Ellipsis.py')
        self.set_and_check(module, astroid.Ellipsis, expected)

    # def test_emptynode(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('nodes/EmptyNode.py')
    #     self.set_and_check(module, astroid.EmptyNode, expected)

    def test_excepthandler(self):
        expected = [(3, 4, 0, 8)]
        module = self.get_file_as_module('nodes/ExceptHandler.py')
        self.set_and_check(module, astroid.ExceptHandler, expected)

    # def test_exec(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('nodes/Exec.py')
    #     self.set_and_check(module, astroid.Exec, expected)

    def test_expr(self):
        """Note: end_col_offset is after the '1' (i.e. astroid.Const last child node) and does not include the last ')'.
        """
        expected = [(1, 1, 0, 7), (2, 2, 0, 9), (3, 3, 0, 8)]
        module = self.get_file_as_module('nodes/Expr.py')
        self.set_and_check(module, astroid.Expr, expected)

    def test_extslice(self):
        expected = [(1, 1, 4, 10)]
        module = self.get_file_as_module('nodes/ExtSlice.py')
        self.set_and_check(module, astroid.ExtSlice, expected)

    def test_for(self):
        expected = [(1, 2, 0, 9)]
        module = self.get_file_as_module('nodes/For.py')
        self.set_and_check(module, astroid.For, expected)

    def test_functiondef(self):
        expected = [(1, 2, 0, 8)]
        module = self.get_file_as_module('nodes/FunctionDef.py')
        self.set_and_check(module, astroid.FunctionDef, expected)

    def test_generatorexp(self):
        expected = [(1, 1, 1, 24)]
        module = self.get_file_as_module('nodes/GeneratorExp.py')
        self.set_and_check(module, astroid.GeneratorExp, expected)

    def test_global(self):
        expected = [(2, 2, 4, 12)]
        module = self.get_file_as_module('nodes/Global.py')
        self.set_and_check(module, astroid.Global, expected)

    def test_if(self):
        expected = [(1, 4, 0, 8), (3, 4, 5, 8)]
        module = self.get_file_as_module('nodes/If.py')
        self.set_and_check(module, astroid.If, expected)

    def test_ifexp(self):
        expected = [(1, 1, 4, 20)]
        module = self.get_file_as_module('nodes/IfExp.py')
        self.set_and_check(module, astroid.IfExp, expected)

    def test_import(self):
        expected = [(1, 1, 0, 14)]
        module = self.get_file_as_module('nodes/Import.py')
        self.set_and_check(module, astroid.Import, expected)

    def test_importfrom(self):
        expected = [(1, 1, 0, 47)]
        module = self.get_file_as_module('nodes/ImportFrom.py')
        self.set_and_check(module, astroid.ImportFrom, expected)

    def test_index(self):
        expected = [(1, 1, 2, 4)]
        module = self.get_file_as_module('nodes/Index.py')
        self.set_and_check(module, astroid.Index, expected)

    def test_keyword(self):
        expected = [(1, 1, 11, 12)]
        module = self.get_file_as_module('nodes/Keyword.py')
        self.set_and_check(module, astroid.Keyword, expected)

    def test_lambda(self):
        expected = [(1, 1, 6, 15), (2, 2, 7, 25)]
        module = self.get_file_as_module('nodes/Lambda.py')
        self.set_and_check(module, astroid.Lambda, expected)

    def test_list(self):
        expected = [(1, 1, 0, 2)]
        module = self.get_file_as_module('nodes/List.py')
        self.set_and_check(module, astroid.List, expected)

    def test_listcomp(self):
        expected = [(1, 1, 1, 19)]
        module = self.get_file_as_module('nodes/ListComp.py')
        self.set_and_check(module, astroid.ListComp, expected)

    def test_module(self):
        expected = [(0, 2, 0, 1)]
        module = self.get_file_as_module('nodes/Module.py')
        self.set_and_check(module, astroid.Module, expected)

    def test_name(self):
        expected = [(1, 1, 0, 6)]
        module = self.get_file_as_module('nodes/Name.py')
        self.set_and_check(module, astroid.Name, expected)

    def test_nonlocal(self):
        expected = [(3, 3, 4, 14)]
        module = self.get_file_as_module('nodes/Nonlocal.py')
        self.set_and_check(module, astroid.Nonlocal, expected)

    def test_pass(self):
        expected = [(1, 1, 0, 4)]
        module = self.get_file_as_module('nodes/Pass.py')
        self.set_and_check(module, astroid.Pass, expected)

    # def test_print(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('nodes/Print.py')
    #     self.set_and_check(module, astroid.Print, expected)

    def test_raise(self):
        expected = [(1, 1, 0, 23)]
        module = self.get_file_as_module('nodes/Raise.py')
        self.set_and_check(module, astroid.Raise, expected)

    # def test_repr(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('nodes/Repr.py')
    #     self.set_and_check(module, astroid.Repr, expected)

    def test_return(self):
        expected = [(1, 1, 0, 8)]
        module = self.get_file_as_module('nodes/Return.py')
        self.set_and_check(module, astroid.Return, expected)

    def test_set(self):
        """Note: col_offset includes '{', but end_col_offset doesn't include '}'
        """
        expected = [(1, 1, 0, 2)]
        module = self.get_file_as_module('nodes/Set.py')
        self.set_and_check(module, astroid.Set, expected)

    def test_setcomp(self):
        expected = [(1, 1, 0, 19)]
        module = self.get_file_as_module('nodes/SetComp.py')
        self.set_and_check(module, astroid.SetComp, expected)

    def test_slice(self):
        """Note: col_offset and end_col_offset are set to the first constant
        encountered, either on left or right side of colon.
        """
        expected = [(1, 1, 2, 3)]
        module = self.get_file_as_module('nodes/Slice.py')
        self.set_and_check(module, astroid.Slice, expected)

    def test_starred(self):
        expected = [(1, 1, 0, 2)]
        module = self.get_file_as_module('nodes/Starred.py')
        self.set_and_check(module, astroid.Starred, expected)

    def test_subscript(self):
        """Note: col_offset includes '[', but end_col_offset doesn't include ']'
        """
        expected = [(1, 1, 0, 3)]
        module = self.get_file_as_module('nodes/Subscript.py')
        self.set_and_check(module, astroid.Subscript, expected)

    def test_tryexcept(self):
        expected = [(1, 4, 0, 8)]
        module = self.get_file_as_module('nodes/TryExcept.py')
        self.set_and_check(module, astroid.TryExcept, expected)

    def test_tryfinally(self):
        expected = [(1, 6, 0, 8)]
        module = self.get_file_as_module('nodes/TryFinally.py')
        self.set_and_check(module, astroid.TryFinally, expected)

    def test_tuple(self):
        expected = [(1, 1, 0, 6), (2, 2, 0, 5)]
        module = self.get_file_as_module('examples/ending_locations/tuple.py')
        self.set_and_check(module, astroid.Tuple, expected)

    def test_unaryop(self):
        expected = [(1, 1, 0, 8)]
        module = self.get_file_as_module('nodes/UnaryOp.py')
        self.set_and_check(module, astroid.UnaryOp, expected)

    def test_while(self):
        expected = [(1, 2, 0, 9)]
        module = self.get_file_as_module('nodes/While.py')
        self.set_and_check(module, astroid.While, expected)

    def test_with(self):
        expected = [(1, 2, 0, 8)]
        module = self.get_file_as_module('nodes/With.py')
        self.set_and_check(module, astroid.With, expected)

    def test_yield(self):
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module('nodes/Yield.py')
        self.set_and_check(module, astroid.Yield, expected)

    def test_yieldfrom(self):
        expected = [(2, 2, 4, 16)]
        module = self.get_file_as_module('nodes/YieldFrom.py')
        self.set_and_check(module, astroid.YieldFrom, expected)


if __name__ == '__main__':
    unittest.main()  # run tests
