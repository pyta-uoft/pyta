"""Tests for setendings.py.

Checks that `end_lineno` and `end_col_offset` node properties are set.
"""
import unittest
from python_ta.transforms.setendings import *
import os.path as path
import sys

# Gives absolute path to root directory
PATH = path.normpath(path.join(path.abspath(__file__), '..', '..', 'examples', 'ending_locations'))


class TestEndingLocations(unittest.TestCase):
    """The method, ending_transformer.visit(module) walks the given astroid
    *tree* and transform each encountered node. Only the nodes which have
    transforms registered will actually be replaced or changed.

    We store the correct values as a tuple:
    (fromlineno, end_lineno, col_offset, end_col_offset)
    """

    def get_file_as_module(self, file_location):
        """Given a filepath (file_location), parse with astroid, and return
        the module.
        """
        file = path.join(PATH, file_location)
        with open(file) as f:
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
        props = [(node.fromlineno, node.end_lineno,
                  node.col_offset, node.end_col_offset)
                 for node in module.nodes_of_class(node_class)
        ]
        self.assertEqual(expected, props)

    def test_arguments(self):
        expected = [(1, 2, 8, 30), (5, 5, 14, 14), (8, 8, 12, 12), (9, 9, 14, 18), (11, 11, 6, 48)]
        module = self.get_file_as_module('arguments.py')
        self.set_and_check(module, astroid.Arguments, expected)

    def test_assert(self):
        expected = [(1, 1, 0, 43), (2, 2, 0, 11)]
        module = self.get_file_as_module('assert.py')
        self.set_and_check(module, astroid.Assert, expected)

    def test_assign(self):
        expected = [(1, 1, 0, 5), (2, 2, 0, 9), (3, 3, 0, 11), (4, 4, 0, 8), (5, 5, 0, 6)]
        module = self.get_file_as_module('assign.py')
        self.set_and_check(module, astroid.Assign, expected)

    def test_assignattr(self):
        """
        Given 'self.name = 10', we want to highlight 'self.name' rather than
        just 'self'.
        """
        expected = [(3, 3, 8, 17), (4, 4, 8, 19)]
        module = self.get_file_as_module('assign_attr.py')
        self.set_and_check(module, astroid.AssignAttr, expected)

    def test_assignname(self):
        expected = [
            (1, 1, 0, 1),
            (2, 2, 0, 1), (2, 2, 4, 5),
            (3, 3, 0, 1), (3, 3, 3, 4),
        ]
        module = self.get_file_as_module('assign_name.py')
        self.set_and_check(module, astroid.AssignName, expected)

    def test_asyncfor(self):
        """Note: col_offset property always set after the 'async' keyword.
        """
        expected = [(3, 7, 4, 16)]
        module = self.get_file_as_module('async_for.py')
        self.set_and_check(module, astroid.AsyncFor, expected)

    def test_asyncfunctiondef(self):
        expected = [(4, 5, 0, 27)]
        module = self.get_file_as_module('async_function_def.py')
        self.set_and_check(module, astroid.AsyncFunctionDef, expected)

    def test_asyncwith(self):
        expected = [(2, 3, 4, 12)]
        module = self.get_file_as_module('async_with.py')
        self.set_and_check(module, astroid.AsyncWith, expected)

    def test_attribute(self):
        """Note: Setting the attribute node by its last child doesn't include
        the attribute in determining the end_col_offset.
        """
        expected = [(1, 1, 0, 12), (2, 2, 0, 14)]
        module = self.get_file_as_module('attribute.py')
        self.set_and_check(module, astroid.Attribute, expected)

    def test_augassign(self):
        expected = [(1, 1, 0, 6)]
        module = self.get_file_as_module('aug_assign.py')
        self.set_and_check(module, astroid.AugAssign, expected)

    def test_await(self):
        expected = [(5, 5, 4, 27)]
        module = self.get_file_as_module('await.py')
        self.set_and_check(module, astroid.Await, expected)

    def test_binop(self):
        expected = [
            (1, 1, 0, 9), (1, 1, 0, 5),
            (2, 2, 0, 13),
            (3, 3, 0, 17),
            (4, 4, 0, 19), (4, 4, 1, 8), (4, 4, 11, 18)
        ]
        module = self.get_file_as_module('bin_op.py')
        self.set_and_check(module, astroid.BinOp, expected)

    def test_boolop(self):
        expected = [(1, 1, 4, 13), (2, 2, 0, 32), (2, 2, 0, 23)]
        module = self.get_file_as_module('bool_op.py')
        self.set_and_check(module, astroid.BoolOp, expected)

    def test_break(self):
        expected = [(2, 2, 4, 9)]
        module = self.get_file_as_module('break.py')
        self.set_and_check(module, astroid.Break, expected)

    def test_call(self):
        expected = [(1, 2, 0, 9)]
        module = self.get_file_as_module('call.py')
        self.set_and_check(module, astroid.Call, expected)

    def test_classdef(self):
        expected = [(1, 3, 0, 8)]
        module = self.get_file_as_module('class_def.py')
        self.set_and_check(module, astroid.ClassDef, expected)

    def test_compare(self):
        expected = [
            (1, 1, 0, 10),
            (2, 2, 0, 5),
            (3, 3, 0, 12),
            (4, 4, 0, 26)
        ]
        module = self.get_file_as_module('compare.py')
        self.set_and_check(module, astroid.Compare, expected)

    def test_comprehension(self):
        """
        Could be in a SetComp, ListComp, or GeneratorExp. In each respective
        case, the subsequent char could be either a brace, bracket, or paren.
        Aside: col_offset should start from beginning of the 'for'.
        """
        expected = [(1, 1, 7, 20), (2, 2, 7, 16), (2, 2, 21, 36), (3, 3, 9, 18), (3, 3, 23, 40)]
        module = self.get_file_as_module('comprehension.py')
        self.set_and_check(module, astroid.Comprehension, expected)

    def test_const(self):
        expected = [(1, 1, 0, 6), (2, 2, 4, 6), (3, 3, 0, 3), (4, 4, 0, 8),
        (5, 7, 0, 1), (8, 8, 6, 11), (8, 8, 13, 25), (9, 9, 0, 3)]
        module = self.get_file_as_module('const.py')
        self.set_and_check(module, astroid.Const, expected)

    def test_continue(self):
        expected = [(2, 2, 4, 12)]
        module = self.get_file_as_module('continue.py')
        self.set_and_check(module, astroid.Continue, expected)

    def test_decorators(self):
        """
        Include the right parens (note: only if decorator takes args)
        """
        expected = [(1, 2, 0, 27), (6, 6, 0, 9)]
        module = self.get_file_as_module('decorators.py')
        self.set_and_check(module, astroid.Decorators, expected)

    def test_delattr(self):
        """Include the 'del' keyword in the col_offset property.
        Include the attribute name in the end_col_offset property.
        """
        expected = [(4, 4, 8, 21), (5, 5, 8, 23)]
        module = self.get_file_as_module('del_attr.py')
        self.set_and_check(module, astroid.DelAttr, expected)

    def test_delete(self):
        """Include the 'del' keyword in the col_offset property.
        """
        expected = [(1, 1, 0, 5), (2, 2, 0, 22)]
        module = self.get_file_as_module('delete.py')
        self.set_and_check(module, astroid.Delete, expected)

    def test_delname(self):
        """Include the 'del' keyword in the col_offset property.
        """
        expected = [(1, 1, 0, 5)]
        module = self.get_file_as_module('del_name.py')
        self.set_and_check(module, astroid.DelName, expected)

    def test_dict(self):
        expected = [(1, 1, 6, 32), (2, 5, 4, 1), (6, 9, 4, 6)]
        module = self.get_file_as_module('dict.py')
        self.set_and_check(module, astroid.Dict, expected)

    def test_dictcomp(self):
        expected = [(1, 1, 0, 29), (2, 2, 0, 37), (3, 7, 0, 1)]
        module = self.get_file_as_module('dict_comp.py')
        self.set_and_check(module, astroid.DictComp, expected)

    # def test_dictunpack(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('DictUnpack.py')
    #     self.set_and_check(module, astroid.DictUnpack, expected)

    # def test_emptynode(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('EmptyNode.py')
    #     self.set_and_check(module, astroid.EmptyNode, expected)

    def test_excepthandler(self):
        expected = [(3, 4, 0, 8)]
        module = self.get_file_as_module('except_handler.py')
        self.set_and_check(module, astroid.ExceptHandler, expected)

    # def test_exec(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('Exec.py')
    #     self.set_and_check(module, astroid.Exec, expected)

    def test_expr(self):
        expected = [(1, 1, 0, 12), (2, 2, 0, 13), (3, 3, 0, 11),
                    (4, 4, 0, 17), (5, 5, 0, 31)]
        module = self.get_file_as_module('expr.py')
        self.set_and_check(module, astroid.Expr, expected)

    def test_extslice(self):
        if sys.version_info >= (3, 9):
            self.skipTest('ExtSlice node is deprecated in Python 3.9')
        expected = [(1, 1, 1, 8), (2, 2, 2, 14), (3, 3, 1, 8), (4, 4, 2, 15), (5, 6, 1, 8)]
        module = self.get_file_as_module('ext_slice.py')
        self.set_and_check(module, astroid.ExtSlice, expected)

    def test_for(self):
        expected = [(1, 4, 0, 8)]
        module = self.get_file_as_module('for.py')
        self.set_and_check(module, astroid.For, expected)

    def test_functiondef(self):
        """Note: this node includes the decorator."""
        expected = [(1, 7, 0, 28)]
        module = self.get_file_as_module('function_def.py')
        self.set_and_check(module, astroid.FunctionDef, expected)

    def test_generatorexp(self):
        expected = [(1, 1, 0, 37), (2, 2, 0, 43)]
        module = self.get_file_as_module('generator_exp.py')
        self.set_and_check(module, astroid.GeneratorExp, expected)

    def test_global(self):
        expected = [(2, 2, 4, 15)]
        module = self.get_file_as_module('global.py')
        self.set_and_check(module, astroid.Global, expected)

    def test_if(self):
        """Note: each elif is represented as a separate If node."""
        expected = [(1, 8, 0, 9), (3, 8, 0, 9),  (5, 8, 0, 9)]
        module = self.get_file_as_module('if.py')
        self.set_and_check(module, astroid.If, expected)

    def test_ifexp(self):
        expected = [(1, 1, 4, 20)]
        module = self.get_file_as_module('if_exp.py')
        self.set_and_check(module, astroid.IfExp, expected)

    def test_import(self):
        expected = [(1, 1, 0, 21), (2, 2, 0, 30), (3, 3, 0, 28)]
        module = self.get_file_as_module('import.py')
        self.set_and_check(module, astroid.Import, expected)

    def test_importfrom(self):
        expected = [(1, 1, 0, 46), (2, 2, 0, 65), (3, 3, 0, 31), (4, 4, 0, 32)]
        module = self.get_file_as_module('import_from.py')
        self.set_and_check(module, astroid.ImportFrom, expected)

    def test_index(self):
        """Should include the enclosing brackets, e.g. "[1]" instead of "1".
        """
        if sys.version_info >= (3, 9):
            self.skipTest('Index node is deprecated in Python 3.9')
        expected = [(1, 1, 1, 5), (2, 2, 2, 10), (3, 3, 2, 15)]
        module = self.get_file_as_module('index.py')
        self.set_and_check(module, astroid.Index, expected)

    def test_keyword(self):
        """Include the name of the keyword, contained in 'node.arg' attribute.
        """
        expected = [(1, 1, 4, 12), (2, 2, 5, 15)]
        module = self.get_file_as_module('keyword.py')
        self.set_and_check(module, astroid.Keyword, expected)

    def test_lambda(self):
        expected = [(1, 1, 6, 15), (2, 2, 7, 25)]
        module = self.get_file_as_module('lambda.py')
        self.set_and_check(module, astroid.Lambda, expected)

    def test_list(self):
        expected = [(1, 1, 0, 2), (2, 2, 0, 9), (3, 3, 0, 6), (4, 9, 0, 1)]
        module = self.get_file_as_module('list.py')
        self.set_and_check(module, astroid.List, expected)

    def test_listcomp(self):
        expected = [(1, 1, 0, 24), (2, 2, 0, 49)]
        module = self.get_file_as_module('list_comp.py')
        self.set_and_check(module, astroid.ListComp, expected)

    def test_module(self):
        expected = [(0, 3, 0, 11)]
        module = self.get_file_as_module('module.py')
        self.set_and_check(module, astroid.Module, expected)

    def test_name(self):
        expected = [(1, 1, 0, 6)]
        module = self.get_file_as_module('name.py')
        self.set_and_check(module, astroid.Name, expected)

    def test_nonlocal(self):
        expected = [(4, 4, 8, 21)]
        module = self.get_file_as_module('nonlocal.py')
        self.set_and_check(module, astroid.Nonlocal, expected)

    def test_pass(self):
        expected = [(3, 3, 8, 12)]
        module = self.get_file_as_module('pass.py')
        self.set_and_check(module, astroid.Pass, expected)

    # def test_print(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('Print.py')
    #     self.set_and_check(module, astroid.Print, expected)

    def test_raise(self):
        expected = [(3, 3, 8, 24), (5, 5, 8, 36)]
        module = self.get_file_as_module('raise.py')
        self.set_and_check(module, astroid.Raise, expected)

    # def test_repr(self):
    #     """NODE EXAMPLE DOES NOT EXIST
    #     """
    #     expected = []
    #     module = self.get_file_as_module('Repr.py')
    #     self.set_and_check(module, astroid.Repr, expected)

    def test_return(self):
        expected = [(3, 3, 8, 14), (5, 5, 8, 42)]
        module = self.get_file_as_module('return.py')
        self.set_and_check(module, astroid.Return, expected)

    def test_set(self):
        expected = [(1, 1, 0, 3), (2, 2, 0, 6), (3, 3, 0, 12)]
        module = self.get_file_as_module('set.py')
        self.set_and_check(module, astroid.Set, expected)

    def test_setcomp(self):
        expected = [(1, 1, 0, 25), (2, 2, 0, 63)]
        module = self.get_file_as_module('set_comp.py')
        self.set_and_check(module, astroid.SetComp, expected)

    def test_slice(self):
        """Note: includes square brackets."""
        expected = [(1, 1, 1, 4),
                    (2, 2, 2, 9),
                    (3, 3, 1, 5),
                    (4, 4, 2, 14),
                    (5, 5, 1, 9),
                    (6, 6, 7, 31),
                    (7, 8, 1, 3),
                    (9, 9, 1, 5),
                    (9, 9, 5, 8),
                    (10, 10, 1, 4),
                    (10, 10, 4, 8),
                    (11, 11, 1, 4),
                    (11, 11, 4, 7),
                    (12, 12, 1, 5),
                    (13, 13, 1, 4),
                    (13, 13, 9, 12),
                    (14, 14, 5, 12),
                    (15, 15, 1, 4),
                    (15, 15, 4, 7),
                    (15, 15, 8, 11)
                    ]
        module = self.get_file_as_module('slice.py')
        self.set_and_check(module, astroid.Slice, expected)

    def test_starred(self):
        expected = [(1, 1, 0, 2), (4, 4, 6, 8)]
        module = self.get_file_as_module('starred.py')
        self.set_and_check(module, astroid.Starred, expected)

    def test_subscript(self):
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
                    (16, 16, 4, 12),
                    (22, 22, 17, 26),
                    (22, 22, 31, 40)
                    ]
        module = self.get_file_as_module('subscript.py')
        self.set_and_check(module, astroid.Subscript, expected)

    def test_tryexcept(self):
        expected = [(1, 4, 0, 8)]
        module = self.get_file_as_module('try_except.py')
        self.set_and_check(module, astroid.TryExcept, expected)

    def test_tryfinally(self):
        expected = [(1, 6, 0, 8)]
        module = self.get_file_as_module('try_finally.py')
        self.set_and_check(module, astroid.TryFinally, expected)

    def test_tuple(self):
        expected = [(1, 1, 0, 6), (2, 2, 0, 11), (3, 3, 0, 5), (4, 4, 0, 7),
                    (5, 5, 0, 12), (6, 8, 0, 8), (9, 9, 0, 4), (10, 10, 0, 7),
                    (11, 13, 0, 17), (14, 14, 0, 6), (15, 15, 7, 13),
                    (16, 16, 4, 10), (17, 17, 0, 10), (17, 17, 0, 4),
                    (17, 17, 6, 10), (18, 18, 0, 6), (20, 20, 0, 6),
                    (21, 21, 0, 2)
                    ]
        module = self.get_file_as_module('tuple.py')
        self.set_and_check(module, astroid.Tuple, expected)

    def test_unaryop(self):
        expected = [(1, 1, 0, 8), (2, 2, 0, 2), (3, 3, 0, 2), (4, 4, 0, 3)]
        module = self.get_file_as_module('unary_op.py')
        self.set_and_check(module, astroid.UnaryOp, expected)

    def test_while(self):
        expected = [(1, 5, 0, 13)]
        module = self.get_file_as_module('while.py')
        self.set_and_check(module, astroid.While, expected)

    def test_with(self):
        expected = [(1, 3, 0, 19)]
        module = self.get_file_as_module('with.py')
        self.set_and_check(module, astroid.With, expected)

    def test_yield(self):
        expected = [(2, 2, 4, 11)]
        module = self.get_file_as_module('yield.py')
        self.set_and_check(module, astroid.Yield, expected)

    def test_yieldfrom(self):
        expected = [(2, 2, 4, 23)]
        module = self.get_file_as_module('yield_from.py')
        self.set_and_check(module, astroid.YieldFrom, expected)


if __name__ == '__main__':
    unittest.main()  # run tests
