"""Unittest for the type_inference_visitor."""

import unittest
from astroid.transforms import TransformVisitor
import astroid
from type_inference_visitor import *

type_visitor = TransformVisitor()
type_visitor.register_transform(astroid.Const, set_const_type_constraints)
type_visitor.register_transform(astroid.Tuple, set_tuple_type_constraints)
type_visitor.register_transform(astroid.List, set_list_type_constraints)
type_visitor.register_transform(astroid.Dict, set_dict_type_constraints)
type_visitor.register_transform(astroid.UnaryOp, set_unaryop_type_constraints)
type_visitor.register_transform(astroid.BinOp, set_binop_type_constraints)


class SetConstFunctionTest(unittest.TestCase):
    """testers specifically for the function set_const using single nodes."""

    def test_const_str(self):
        """testing if the function set_const has the correct output for node
        type str."""
        # can't work without assigning, string will be evaluated to a Name Obj.
        module = astroid.parse("""a='sample_string'""")
        type_visitor.visit(module)
        expected = str
        # module is a module() object, module.body is a list object,
        # module.body[0] is an Assign object, module.body[0].value is a
        # Const(str) node.
        self.assertEqual(expected, module.body[0].value.type_constraints)

    def test_const_int(self):
        """testing if the function set_const has the correct output for node
        type int."""
        module = astroid.parse("""100""")
        type_visitor.visit(module)
        expected = int
        self.assertEqual(expected, module.body[0].value.type_constraints)

    def test_const_float(self):
        """testing if the function set_const has the correct output for node
        type float."""
        module = astroid.parse("""100.01""")
        type_visitor.visit(module)
        expected = float
        self.assertEqual(expected, module.body[0].value.type_constraints)

    def test_const_bool(self):
        """testing if the function set_const has the correct output for node
        type boolean."""
        module = astroid.parse("""True""")
        type_visitor.visit(module)
        expected = bool
        self.assertEqual(expected, module.body[0].value.type_constraints)

    def test_const_none(self):
        """testing if the function set_const has the correct output for
        NoneType node."""
        module = astroid.parse("""None""")
        type_visitor.visit(module)
        expected = type(None)
        self.assertEqual(expected, module.body[0].value.type_constraints)


class TypeInferenceVisitorTest(unittest.TestCase):
    """testers for type_inference_visitor. Modules are been passed in instead
    of single nodes."""

    def test_binop_same_type_operands(self):
        """testing if a binary operator passed into TypeVisitor
        has the correct type_constraints attribute when both operands have
        the same type.

        Note: astroid.parse() and type_visitor both have a return type
        Module(), if we directly look for nodes under Module(), the node
        binop will not be returned, but instead, it will be a wrapper for
        binop -> astroid.Expr. To find the binop wrapped by the Expr node,
        we need to use Expr.value. So binop is 2 layers under the return
        type of astroid.parse and type_visitor.visit (binop is 2 layers
        under module).

        An example from AST:
        > parseprint('-a')
        Module(body=[
        Expr(value=UnaryOp(op=USub(), operand=Name(id='a', ctx=Load()))),
        ])
        """
        module = astroid.parse("""10 + 2""")    # int
        visited_module = type_visitor.visit(module)
        self.assertEqual(int, visited_module.body[0].value.type_constraints)

    def test_binop_diff_type_operands(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when operands have different types.
        """
        module = astroid.parse("""6 + 0.3""")   # float
        visited_module = type_visitor.visit(module)
        self.assertEqual(float, visited_module.body[0].value.type_constraints)

    def test_unary(self):
        """testing if a unary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute.
        """
        module = astroid.parse("""-2""")    # int
        visited_module = type_visitor.visit(module)
        self.assertEqual(int, visited_module.body[0].value.type_constraints)

    def test_list_same_type_elements(self):
        """testing if a list that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The list contains only 1 type of elements.
        """
        module = astroid.parse("""['hi', 'how', 'is', 'life']""")  # List(str)
        visited_module = type_visitor.visit(module)
        self.assertEqual(List[str], visited_module.body[
            0].value.type_constraints)

    def test_list_different_type_elements(self):
        """testing if a list that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The list contains different type of elements.
        """
        module = astroid.parse("""[1, 2, 2.5, 3, 'cheese']""")  # List
        visited_module = type_visitor.visit(module)
        self.assertEqual(List, visited_module.body[0].value.type_constraints)

    def test_tuple_same_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 same type of elements.
        """
        module = astroid.parse("""(1, 2)""")    # Tuple[int, int]
        visited_module = type_visitor.visit(module)
        self.assertEqual(Tuple[int, int], visited_module.body[
            0].value.type_constraints)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 different type of elements.
        """
        module = astroid.parse("""('GPA', 4.0)""")
        visited_module = type_visitor.visit(module)
        self.assertEqual(Tuple[str, float], visited_module.body[
            0].value.type_constraints)

    def test_dict_same_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains same type of elements.

        Note: parameter of Dict[] must be 2 or 0. Even if a Dict object only
        contains a single type(call it type1), the type_constraints of this
        Dict object has to be set as Dict[type1, type1].
        """
        module = astroid.parse("""{'a':'one', 'b':'two'}""")  # Dict[str, str]
        visited_module = type_visitor.visit(module)
        self.assertEqual(Dict[str, str],
                         visited_module.body[0].value.type_constraints)

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
        module = astroid.parse("""{'a': 1, 'b': 2}""")  # Dict[str, int]
        visited_module = type_visitor.visit(module)
        self.assertEqual(Dict[str, int], visited_module.body[
            0].value.type_constraints)

    def test_dict_multi_diff_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains more than 2 different types of elements.
        """
        module = astroid.parse("""{'a': 1, 0.25:True}""")  # Dict
        visited_module = type_visitor.visit(module)
        self.assertEqual(Dict, visited_module.body[0].value.type_constraints)


class TypeInferenceVisitorTestMoreComplexed(unittest.TestCase):

    def test_multi_unary(self):
        module = astroid.parse("""-(+(-(+(-1))))""")  # int
        visited_module = type_visitor.visit(module)
        self.assertEqual(int, visited_module.body[0].value.type_constraints)

    def test_binop_multiple_operands_same_type(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have same types.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 + 5""")   # int
        visited_module = type_visitor.visit(module)
        self.assertEqual(int, visited_module.body[0].value.type_constraints)

    def test_binop_multiple_operands_different_type(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have different types.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 - 5.5""")   # float
        visited_module = type_visitor.visit(module)
        self.assertEqual(float, visited_module.body[0].value.type_constraints)

    def test_binop_multiple_operands_different_type_with_brackets(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when multiple operands have different types with brackets.
        """
        module = astroid.parse("""1 + 2 + 3 + 4 - (5.5 + 4.5)""")   # float
        visited_module = type_visitor.visit(module)
        self.assertEqual(float, visited_module.body[0].value.type_constraints)

    def test_tuple_same_type_multi_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains same type of multiple elements.
        """
        module = astroid.parse("""(1, 2, 3, 4, 5, 6)""")  # Tuple[int]
        visited_module = type_visitor.visit(module)
        self.assertEqual(Tuple[int, int, int, int, int, int],
                         visited_module.body[0].value.type_constraints)

    def test_nested_list(self):
        """testing if a nested list that's been passed into TypeVisitor
        has the correct type_constraints attribute.
        """
        module = astroid.parse("""[1, [[2, 2.5], [3, 'a']]]""")  # List
        visited_module = type_visitor.visit(module)
        self.assertEqual(List, visited_module.body[0].value.type_constraints)

    def test_dict_with_key_tuple_value_list(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains list and tuple.
        """
        module = astroid.parse("""{(0, 1): [3, 4], (1, 1): [3, 2], (1, 0
        ): [7, 8, 5], (1, 2): [0, 0, 0], (1, 3): [2, 3, 4]}""")
        visited_module = type_visitor.visit(module)
        self.assertEqual(Dict[Tuple[int, int], List[int]], visited_module.body[
            0].value.type_constraints)

    def test_dict_mixed(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains binop, list, tuple, unaryop, str, bool, nested
        tuple and nested list.
        """
        module = astroid.parse("""{(['l', 'a'], 'b'): 'c', (4, 7): 2+5,
        (True): False, ('h', ('i', ('2'))): -7, [1, [3, 4]]: ("that's it")}""")
        visited_module = type_visitor.visit(module)
        self.assertEqual(Dict, visited_module.body[0].value.type_constraints)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains different type of multiple elements.
        """
        module = astroid.parse("""('a', 4.0, 'b', 'c', 'd', True)""")  # Tuple
        visited_module = type_visitor.visit(module)
        self.assertEqual(Tuple[str, float, str, str, str, bool],
                         visited_module.body[0].value.type_constraints)

    def test_nested_tuple(self):
        """testing if a nested tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute..
        """
        module = astroid.parse("""(1, (2, (3, '4')))""")  # Tuple
        visited_module = type_visitor.visit(module)
        self.assertEqual(Tuple[int, Tuple[int, Tuple[int, str]]],
                         visited_module.body[0].value.type_constraints)

    def test_nested_tuple_list(self):
        """testing if a nested tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute..
        """
        module = astroid.parse("""(1, [2, (3, '4')], [True, False,['str1',
        'str2', 6.99, ('bacon', 'salad')]], (False, 'chicken'))""")
        visited_module = type_visitor.visit(module)
        self.assertEqual(Tuple[int, List, List, Tuple[bool, str]],
                         visited_module.body[0].value.type_constraints)


if __name__ == '__main__':
    unittest.main()
