import astroid
import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
from typing import Union
settings.load_profile("pyta")


@given(cs.primitive_values, cs.binary_bool_operator, cs.primitive_values)
def test_binary_boolop(left_operand, operator, right_operand):
    """Test type setting of binary BoolOp node(s)."""
    program = f'{repr(left_operand)} {operator} {repr(right_operand)}\n'
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    expected_type = Union[type(left_operand), type(right_operand)]
    assert boolop_node.type_constraints.type == expected_type


if __name__ == '__main__':
    nose.main()
