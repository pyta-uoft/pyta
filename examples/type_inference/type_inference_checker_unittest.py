"""Unittest for the type_inference_visitor."""

import unittest
import sys
import astroid
from typing import Tuple, List, Dict
from astroid import test_utils
from type_inference_visitor import TypeVisitor, set_const, set_binop, \
    set_unaryop, set_dict, set_list, set_tuple


class SetConstFunctionTest(unittest.TestCase):
    """testers specifically for the function set_const using single nodes."""

    def test_const_str(self):
        """testing if the function set_const has the correct output for node
        type str."""
        expected = str
        node = test_utils.extract_node("""a = __('sample_string')""")
        set_const(node)
        self.assertEqual(expected, node.type_constraints)

    def test_const_int(self):
        """testing if the function set_const has the correct output for node
        type int."""
        expected = int
        node = test_utils.extract_node("""a = __(5)""")
        set_const(node)
        self.assertEqual(expected, node.type_constraints)

    def test_const_float(self):
        """testing if the function set_const has the correct output for node
        type float."""
        expected = float
        node = test_utils.extract_node("""a = __(2.18)""")
        set_const(node)
        self.assertEqual(expected, node.type_constraints)

    def test_const_bool(self):
        """testing if the function set_const has the correct output for node
        type boolean."""
        expected = bool
        node = test_utils.extract_node("""a = __(True)""")
        set_const(node)
        self.assertEqual(expected, node.type_constraints)

    def test_const_none(self):
        """testing if the function set_const has the correct output for
        NoneType node."""
        expected = type(None)
        node = test_utils.extract_node("""a = __(None)""")
        set_const(node)
        self.assertEqual(expected, node.type_constraints)


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
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.BinOp, set_binop)
        module = astroid.parse("""10 + 2""")    # int
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = int
        self.assertEqual(expected, result)

    def test_binop_diff_type_operands(self):
        """testing if a binary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute
        when operands have different types.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.BinOp, set_binop)
        module = astroid.parse("""6 + 0.3""")   # float
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = float
        self.assertEqual(expected, result)

    def test_unary(self):
        """testing if a unary operator that's been passed into
        TypeVisitor has the correct type_constraints attribute.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.UnaryOp, set_unaryop)
        module = astroid.parse("""-2""")    # int
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = int
        self.assertEqual(expected, result)

    def test_list_same_type_elements(self):
        """testing if a list that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The list contains only 1 type of elements.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.List, set_list)
        module = astroid.parse("""['hi', 'how', 'is', 'life']""")  # List(str)
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = List[str]
        self.assertEqual(expected, result)

    def test_list_different_type_elements(self):
        """testing if a list that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The list contains different type of elements.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.List, set_list)
        module = astroid.parse("""[1, 2, 2.5, 3, 'cheese']""")  # List
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = List
        self.assertEqual(expected, result)

    def test_tuple_same_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 same type of elements.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.Tuple, set_tuple)
        module = astroid.parse("""(1, 2)""")    # Tuple[int, int]
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = Tuple[int, int]
        self.assertEqual(expected, result)

    def test_tuple_diff_type_elements(self):
        """testing if a tuple that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The tuple contains 2 different type of elements.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.Tuple, set_tuple)
        module = astroid.parse("""('GPA', 4.0)""")    # Tuple[str, float]
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = Tuple[str, float]
        self.assertEqual(expected, result)

    def test_dict_same_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains same type of elements.

        Note: parameter of Dict[] must be 2 or 0. Even if a Dict object only
        contains a single type(call it type1), the type_constraints of this
        Dict object has to be set as Dict[type1, type1].
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.Dict, set_dict)
        module = astroid.parse("""{'a':'one', 'b':'two'}""")  # Dict[str, str]
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = Dict[str, str]
        self.assertEqual(expected, result)

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
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.Dict, set_dict)
        module = astroid.parse("""{'a': 1, 'b': 2}""")  # Dict[str, int]
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = Dict[str, int]
        self.assertEqual(expected, result)

    def test_dict_multi_diff_type_elements(self):
        """testing if a dict that's been passed into TypeVisitor
        has the correct type_constraints attribute.

        The dict contains more than 2 different types of elements.
        """
        type_visitor = TypeVisitor()
        type_visitor.register_transform(astroid.Const, set_const)
        type_visitor.register_transform(astroid.Dict, set_dict)
        module = astroid.parse("""{'a': 1, 0.25:True}""")  # Dict
        transformed_module = type_visitor.visit(module)
        for node in transformed_module.body:
            result = node.value.type_constraints
        expected = Dict
        self.assertEqual(expected, result)


if __name__ == '__main__':
    unittest.main()
