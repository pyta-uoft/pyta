import astroid
import nose
from hypothesis import given, settings, assume
import hypothesis.strategies as hs
import tests.custom_hypothesis_support as cs
from typing import Any, Union
settings.load_profile("pyta")


@given(cs.binary_bool_operator, cs.homogeneous_list(min_size=2))
def test_homogeneous_binary_boolop(op, operand_list):
    """Test type setting of binary BoolOp node(s) representing expression with homogeneous operands."""
    pre_format_program = [repr(operand) for operand in operand_list]
    program = (' ' + op + ' ').join(pre_format_program)
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    assert boolop_node.type_constraints.type == type(operand_list[0])


@given(cs.binary_bool_operator, cs.random_list(min_size=2))
def test_heterogeneous_binary_boolop(op, operand_list):
    """Test type setting of binary BoolOp node(s) representing expression with heterogeneous operands."""
    assume(not isinstance(operand_list[0], type(operand_list[1])))
    pre_format_program = [repr(operand) for operand in operand_list]
    program = (' ' + op + ' ').join(pre_format_program)
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    assert boolop_node.type_constraints.type == Any


if __name__ == '__main__':
    nose.main()
