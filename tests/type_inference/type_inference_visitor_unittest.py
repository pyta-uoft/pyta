"""Unittest for the type_inference_visitor."""

import unittest

from astroid import node_classes
from python_ta.transforms.type_inference_visitor import *


class BinOpTests(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        # Instantiate a visitor, and register the transform functions to it.
        self.type_visitor = register_type_constraints_setter()

    def test_str(self):
        module = astroid.parse("""[1, 2, 'aaa' + 'bbb']""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([str], result)

    def test_str_multiplication(self):
        module = astroid.parse("""[1, 2, 'ccc' * 3]""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([str], result)

    def test_list_of_str(self):
        module = astroid.parse("""['a', 'b'] + ['c', 'd']""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([List[str]], result)

    def test_mixed_list(self):
        module = astroid.parse("""['a', 'b'] + [1, 2]""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([List[Any]], result)

    def test_list_multiplication(self):
        module = astroid.parse("""[1, True] * 2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([List[Any]], result)

    def test_list_multiplication2(self):
        module = astroid.parse("""3 * ['abc', 'def', 'gcd']""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([List[str]], result)

    def test_tuple_of_int(self):
        module = astroid.parse("""(1, 2) + (3, 4)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([Tuple[int, int, int, int]], result)

    def test_mixed_tuple(self):
        module = astroid.parse("""('a', 'b') + (1, 2)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([Tuple[str, str, int, int]], result)

    # def test_tuple_multiplication(self):
    #     module = astroid.parse("""(1, 2) * 2""")
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.BinOp)]
    #     self.assertEqual([Tuple[int, int, int, int]], result)
    #
    # def test_tuple_multiplication2(self):
    #     module = astroid.parse("""3 * ('abc', 'def', 'gcd')""")
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.BinOp)]
    #     self.assertEqual([Tuple[str, str, str, str, str, str, str, str, str]],
    #                      result)

    def test_int_with_parentheses(self):
        module = astroid.parse("""(2) * 6""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([int], result)

    def test_float_with_parentheses(self):
        module = astroid.parse("""(2.2) * 6""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_float_with_power(self):
        module = astroid.parse("""(2.2) ** 1.2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_int_with_power(self):
        module = astroid.parse("""2 ** 3""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([int], result)

    def test_int_float_with_power(self):
        module = astroid.parse("""2.2 ** 6""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_modulus0(self):
        module = astroid.parse("""(2.2) % 1.2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_modulus1(self):
        module = astroid.parse("""23 % 3""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([int], result)

    def test_modulus2(self):
        module = astroid.parse("""2.2 % 6""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_floordiv0(self):
        module = astroid.parse("""(2.2) // 1.223332""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_floordiv1(self):
        module = astroid.parse("""23 // 300""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([int], result)

    def test_floordiv2(self):
        module = astroid.parse("""2.2212 // 600""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_div0(self):
        module = astroid.parse("""2.2212 / 600""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_div1(self):
        module = astroid.parse("""300 / 600""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_div2(self):
        module = astroid.parse("""1200 / 600""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float], result)


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
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([int], result)

    def test_binop_diff_type_operands(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when operands have different types.
        """
        module = astroid.parse("""6 + 0.3""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(node_classes.BinOp)]
        self.assertEqual([float], result)

    def test_unary(self):
        """testing if a unary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute.
        """
        module = astroid.parse("""-2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.UnaryOp)]
        self.assertEqual([int], result)

    def test_tuple_same_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 same type of elements.
        """
        module = astroid.parse("""(1, 2)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[int, int]], result)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 different type of elements.
        """
        module = astroid.parse("""('GPA', 4.0)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
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
        result = [n.type_constraints.type for n in module.nodes_of_class(
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
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict[str, int]], result)

    def test_dict_multi_diff_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains more than 2 different types of elements.
        """
        module = astroid.parse("""{'a': 1, 0.25:True}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict], result)

    def test_multi_unary(self):
        module = astroid.parse("""-(+(-(+(-1))))""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
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
        result = [n.type_constraints.type for n in module.nodes_of_class(
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
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float, int, int, int], result)

    def test_binop_multiple_operands_different_type_with_brackets(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have different types with brackets.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 - (5.5 + 4.5)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BinOp)]
        self.assertEqual([float, int, int, int, float], result)

    def test_tuple_same_type_multi_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains same type of multiple elements.
        """
        module = astroid.parse("""(1, 2, 3, 4, 5, 6)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[int, int, int, int, int, int]], result)

    def test_nested_list(self):
        """testing if a nested list that's been passed into TypeVisitor
        has the correct type_constraints attribute.
        """
        module = astroid.parse("""[1, [[2, 2.5], [3, 'a']]]""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.List)]
        self.assertEqual(List[Any], result[0])

    def test_dict_with_key_tuple_value_list(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains list and tuple.
        """
        module = astroid.parse("""{(0, 1): [3, 4], (1, 1): [3, 2], (1, 0
        ): [7, 8, 5], (1, 2): [0, 0, 0], (1, 3): [2, 3, 4]}""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
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
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Dict)]
        self.assertEqual([Dict], result)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains different type of multiple elements.
        """
        module = astroid.parse("""('a', 4.0, 'b', 'c', 'd', True)""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual([Tuple[str, float, str, str, str, bool]], result)

    def test_nested_tuple(self):
        """testing if a nested tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute..
        """
        module = astroid.parse("""(1, (2, (3, '4')))""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual(Tuple[int, Tuple[int, Tuple[int, str]]], result[0])

    def test_nested_tuple_list(self):
        """testing if a nested tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute..
        """
        module = astroid.parse("""(1, [2, (3, '4')], [True, False,['str1',
        'str2', 6.99, ('bacon', 'salad')]], (False, 'chicken'))""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Tuple)]
        self.assertEqual(Tuple[int, List[Any], List[Any], Tuple[bool, str]], result[0])

    # def test_subscript0(self):
    #     test_block = """
    #     list_a = [1, 2, [1, 2, 3], 4]
    #     list_a[2]
    #     """
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([List[int]], result)
    #
    # def test_subscript0(self):
    #     test_block = """
    #     list_a = [1, 2, 'string', 4]
    #     list_a[2]
    #     """
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([str], result)
    #
    # def test_subscript1(self):
    #     test_block = """
    #     list_a = [1, 2, [True, True, False], 4]
    #     list_a[2]
    #     """
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([List[bool]], result)
    #
    # def test_subscript2(self):
    #     test_block = """
    #     tuple_a = ('a', 'b', 'Happy', 'Halloweeeeeen!')
    #     tuple_a[2]
    #     """
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([str], result)
    #
    # def test_subscript3(self):
    #     test_block = """
    #         tuple_a = ('a', 'b', ('Happy', 'Halloweeeeeen!'))
    #         tuple_a[2][0]
    #         """
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([str, Tuple[str, str]], result)
    #
    # def test_subscript4(self):
    #     test_block = """
    #         dict_a = {'index_1' : 'book', 'index_2': None, 'index_3': 'cat'}
    #         dict_a['index_2']
    #         """
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([type(None)], result)
    #
    # def test_subscript5(self):
    #     test_block = """
    #         string_a = "I'm a string tester!"
    #         string_a[1]
    #         """
    #     # problem encountered: we should be able to directly
    #     module = astroid.parse(test_block)
    #     self.type_visitor.visit(module)
    #     result = [n.type_constraints.type for n in module.nodes_of_class(
    #         node_classes.Subscript)]
    #     self.assertEqual([str], result)

    def test_compare0(self):
        module = astroid.parse("""1 < 2""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_compare1(self):
        module = astroid.parse("""[1, 2, 3] <= [4, 5]""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_compare2(self):
        code = """
        a = 'forest'
        b = 'gold'
        a >= b
        """
        module = astroid.parse(code)
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_compare3(self):
        module = astroid.parse("True != False")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_compare4(self):
        module = astroid.parse("[1, 2, 3] is List")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_compare5(self):
        module = astroid.parse("[1, 1, 1] is not [1, 1, 1]")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_compare6(self):
        module = astroid.parse("[1, 1, 1] not in (1, 2)")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.Compare)]
        self.assertEqual([bool], result)

    def test_bool0(self):
        module = astroid.parse("""99 or 100""")
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BoolOp)]
        self.assertEqual([int], result)

    def test_bool2(self):
        code = """
            bool1 = 0 or "abcde"
            bool2 = "abcde" and 0
            bool3 = 0 and "abcde"
        """
        module = astroid.parse(code)
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BoolOp)]
        self.assertEqual([int, int, str], result)

    def test_bool3(self):
        code = """
            bool1 = "String1" and "String2"
            bool2 = (not True) and (not 7)
            bool3 = False and (not not 7)
        """
        module = astroid.parse(code)
        self.type_visitor.visit(module)
        result = [n.type_constraints.type for n in module.nodes_of_class(
            node_classes.BoolOp)]
        self.assertEqual([str, int, int], result)


if __name__ == '__main__':
    unittest.main()
