"""Unittest for the type_inference_visitor."""

import unittest

from astroid import node_classes
from python_ta.transforms.type_inference_visitor import *


class SetConstFunctionTest(unittest.TestCase):
    """testers specifically for the function set_const using single nodes."""

    @classmethod
    def setUpClass(self):
        # Instantiate a visitor, and register the transform functions to it.
        self.type_visitor = register_type_constraints_setter()

    def test_const_str(self):
        """testing if the function set_const has the correct output for node
        type str."""
        module = astroid.parse("""a='sample_string'""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Const) if type(n.value) == str]
        self.assertEqual([str], result)

    def test_const_int(self):
        """testing if the function set_const has the correct output for node
        type int."""
        module = astroid.parse("""100""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Const) if type(n.value) == int]
        self.assertEqual([int], result)

    def test_const_float(self):
        """testing if the function set_const has the correct output for node
        type float."""
        module = astroid.parse("""100.01""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Const) if type(n.value) == float]
        self.assertEqual([float], result)

    def test_const_bool(self):
        """testing if the function set_const has the correct output for node
        type boolean."""
        module = astroid.parse("""True""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Const) if type(n.value) == bool]
        self.assertEqual([bool], result)

    def test_const_none(self):
        """testing if the function set_const has the correct output for
        NoneType node."""
        module = astroid.parse("""None""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Const) if type(n.value) == type(None)]
        self.assertEqual([type(None)], result)


class TypeInferenceVisitorTest(unittest.TestCase):
    """testers for type_inference_visitor. Modules are been passed in instead
    of single nodes."""

    @classmethod
    def setUpClass(self):
        # Instantiate a visitor, and register the transform functions to it.
        self.type_visitor = register_type_constraints_setter()

    def test_binop_same_type_operands(self):
        """testing if a binary operator passed into TypeVisitor
        has the correct type_constraints attribute when both operands have
        the same type.
        """
        module = astroid.parse("""10 + 2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([int], result)

    def test_binop_diff_type_operands(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when operands have different types.
        """
        module = astroid.parse("""6 + 0.3""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_unary(self):
        """testing if a unary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute.
        """
        module = astroid.parse("""-2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.UnaryOp)]
        self.assertEqual([int], result)

    def test_list_same_type_elements(self):
        """testing if a list that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The list contains only 1 type of elements.
        """
        module = astroid.parse("""['hi', 'how', 'is', 'life']""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.List)]
        self.assertEqual([List[str]], result)

    def test_list_different_type_elements(self):
        """testing if a list that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The list contains different type of elements.
        """
        module = astroid.parse("""[1, 2, 2.5, 3, 'cheese']""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.List)]
        self.assertEqual([List], result)

    def test_tuple_same_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 same type of elements.
        """
        module = astroid.parse("""(1, 2)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[int, int]], result)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 different type of elements.
        """
        module = astroid.parse("""('GPA', 4.0)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[str, float]], result)

    def test_dict_same_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains same type of elements.

        Note: parameter of Dict[] must be 2 or 0. Even if a Dict object only
        contains a single type(call it type1), the type_constraints of this
        Dict object has to be set as Dict[type1, type1].
        """
        module = astroid.parse("""{'a':'one', 'b':'two'}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict[str, str]], result)

    def test_dict_2_diff_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains only two different types of elements.

        Note: The reason that a Dict object with 2 different types of elements
        has type_constraints Dict[type1, type2] instead of the general type
        Dict is, when use Typing.Dict, parameter of Dict[] must be 2 or 0.
        Therefore, if the Dict object only contains 1 type, we have to
        return Dict[type1, type1] with a repetition of type1, so I think it
        will be reasonable to show 2 different types as well.
        """
        module = astroid.parse("""{'a': 1, 'b': 2}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict[str, int]], result)

    def test_dict_multi_diff_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains more than 2 different types of elements.
        """
        module = astroid.parse("""{'a': 1, 0.25:True}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict], result)


class TypeInferenceVisitorTestMoreComplex(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        # Instantiate a visitor, and register the transform functions to it.
        self.type_visitor = register_type_constraints_setter()

    def test_multi_unary(self):
        module = astroid.parse("""-(+(-(+(-1))))""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.UnaryOp)]
        # There are 5 Unary Operators, and each one of them has the
        # type_constraints int.
        self.assertEqual([int, int, int, int, int], result)

    def test_binop_multiple_operands_same_type(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have same types.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 + 5""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        # There are 4 Binary Operators, and each one of them has the
        # type_constraints int.
        self.assertEqual([int, int, int ,int], result)

    def test_binop_multiple_operands_different_type(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have different types.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 - 5.5""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float, int, int, int], result)

    def test_binop_multiple_operands_different_type_with_brackets(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have different types with brackets.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 - (5.5 + 4.5)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float, int, int, int, float], result)

    def test_tuple_same_type_multi_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains same type of multiple elements.
        """
        module = astroid.parse("""(1, 2, 3, 4, 5, 6)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[int, int, int, int, int, int]], result)

    def test_nested_list(self):
        """testing if a nested list that's been passed into TypeVisitor
        has the correct type_constraints attribute.
        """
        module = astroid.parse("""[1, [[2, 2.5], [3, 'a']]]""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.List)]
        self.assertEqual(List, result[0])

    def test_dict_with_key_tuple_value_list(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains list and tuple.
        """
        module = astroid.parse("""{(0, 1): [3, 4], (1, 1): [3, 2], (1, 0
        ): [7, 8, 5], (1, 2): [0, 0, 0], (1, 3): [2, 3, 4]}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict[Tuple[int, int], List[int]]], result)

    def test_dict_mixed(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains binop, list, tuple, unaryop, str, bool, nested
        tuple and nested list.
        """
        module = astroid.parse("""{(['l', 'a'], 'b'): 'c', (4, 7): 2+5,
        (True): False, ('h', ('i', ('2'))): -7, [1, [3, 4]]: ("that's it")}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict], result)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains different type of multiple elements.
        """
        module = astroid.parse("""('a', 4.0, 'b', 'c', 'd', True)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[str, float, str, str, str, bool]], result)

    def test_nested_tuple(self):
        """testing if a nested tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute..
        """
        module = astroid.parse("""(1, (2, (3, '4')))""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual(Tuple[int, Tuple[int, Tuple[int, str]]], result[0])

    def test_nested_tuple_list(self):
        """testing if a nested tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute..
        """
        module = astroid.parse("""(1, [2, (3, '4')], [True, False,['str1',
        'str2', 6.99, ('bacon', 'salad')]], (False, 'chicken'))""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual(Tuple[int, List, List, Tuple[bool, str]], result[0])


class MoreTupleTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        # Instantiate a visitor, and register the transform functions to it.
        self.type_visitor = register_type_constraints_setter()

    def test_list_of_str(self):
        module = astroid.parse("""['a', 'b'] + ['c', 'd']""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([List[str]], result)

    def test_mixed_list(self):
        module = astroid.parse("""['a', 'b'] + [1, 2]""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([List], result)

    def test_tuple_of_int(self):
        module = astroid.parse("""(1, 2) + (3, 4)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([Tuple[int, int]], result)

    def test_mixed_tuple(self):
        module = astroid.parse("""('a', 'b') + (1, 2)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        # for the type_constraints of binop which has tuple type of operands,
        # does all elements type from both operands need to be listed?
        self.assertEqual([Tuple], result)

    def test_dict_of_str_int(self):
        module = astroid.parse("""{'a': 1} + {'b': 2}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([Dict[str, int]], result)

    def test_mixed_dict(self):
        module = astroid.parse("""{'a': 1} + {'b': 'c'}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([Dict], result)

if __name__ == '__main__':
    unittest.main()
