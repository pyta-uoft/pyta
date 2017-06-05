import astroid
import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.primitive_values, cs.binary_bool_operator, cs.primitive_values)
def test_binary_boolop(left_operand, operator, right_operand):
    """Test type setting of binary BoolOp node(s)."""
    # negative numbers seen as UnaryOp node; type_constraints for UnaryOps is not supported yet.
    if isinstance(left_operand, int):
        assume(left_operand > 0)
    if isinstance(right_operand, int):
        assume(right_operand > 0)
    # must account for empty string, which is invalid operand; assume seems better than changing strategy.
    if isinstance(left_operand, str):
        assume(len(left_operand) > 0)
    if isinstance(right_operand, str):
        assume(len(right_operand) > 0)
    program = f'{repr(left_operand)} {operator} {repr(right_operand)}\n'
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    if operator == 'or':
        if not left_operand:
            expected_type = type(right_operand)
        else:
            expected_type = type(left_operand)
    elif operator == 'and':
        if not left_operand:
            expected_type = type(left_operand)
        else:
            expected_type = type(right_operand)
    assert boolop_node.type_constraints.type == expected_type


# @given(cs.unary_bool_op, cs.bool_value)
# def test_not_boolop_concrete(operator, operand):
#     """Test type setting of unary BoolOp node(s)"""
#     try:
#         exp_func_type = TYPE_STORE.lookup_function(op_to_dunder(operator), type(operand))
#         exp_return_type = exp_func_type.__args__[-1]
#     except KeyError:
#         exp_return_type = None
#     assume(exp_return_type is not None)
#     program = f'{operator} {repr(operand)}\n'
#     module = cs._parse_text(program)
#     boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
#     assert boolop_node.type_constraints.type == exp_return_type


if __name__ == '__main__':
    nose.main()
