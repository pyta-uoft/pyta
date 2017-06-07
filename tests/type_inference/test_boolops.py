import astroid
import nose
from hypothesis import given, settings, assume
import hypothesis.strategies as hs
import tests.custom_hypothesis_support as cs
from typing import Any, Union
settings.load_profile("pyta")


@given(cs.binary_bool_operator, hs.lists(cs.primitive_values))
def test_homogeneous_binary_boolop(op, operand_list):
    """Test type setting of binary BoolOp node(s) representing expression with same binary boolean operations."""
    # get every permutation?
    assume(len(operand_list) > 1)
    pre_format_program = [repr(operand) for operand in operand_list]
    program = (' ' + op + ' ').join(pre_format_program)
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    operand_type = type(operand_list[0])
    homogeneous = True
    for operand in operand_list:
        if type(operand) != operand_type:
            homogeneous = False
            break
    if not homogeneous:
        expected_type = Any
    else:
        expected_type = operand_type
    assert boolop_node.type_constraints.type == expected_type


# @given(hs.lists(cs.binary_bool_operator), hs.lists(cs.primitive_values))
# def test_heterogeneous_binary_boolop(op_list, operand_list):
#     """Test type setting of binary BoolOp node(s) representing expression with different binary boolean operations."""
#     assume(len(op_list) > 0 and len(operand_list) == len(op_list) + 1)
#     pre_format_program = [str(pair) for operand_op_pair in zip(operand_list[:-1], op_list) for pair in operand_op_pair]
#     pre_format_program.append(repr(operand_list[-1]))
#     program = ' '.join(pre_format_program)
#     module = cs._parse_text(program)
#     boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
#     operand_type = type(operand_list[0])
#     homogeneous = True
#     for operand in operand_list:
#         if type(operand) != operand_type:
#             homogeneous = False
#             break
#     if not homogeneous:
#         expected_type = Any
#     else:
#         expected_type = operand_type
#     a = boolop_node.type_constraints.type
#     assert boolop_node.type_constraints.type == expected_type


if __name__ == '__main__':
    nose.main()
