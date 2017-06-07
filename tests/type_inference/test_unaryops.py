import astroid
import nose
from hypothesis import given, settings
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.non_bool_unary_op, cs.primitive_values)
def test_unarynop_non_bool_concrete(operator, operand):
    """Test type setting of UnaryOp node(s) with non-boolean operand."""
    program = f'{operator} {repr(operand)}\n'
    module = cs._parse_text(program)
    unaryop_node = list(module.nodes_of_class(astroid.UnaryOp))[0]
    assert isinstance(unaryop_node.type_constraints.type, type(bool))


@given(cs.unary_bool_operator, cs.primitive_values)
def test_not_bool(operator, operand):
    """Test type setting of UnaryOp node representing boolean operation not _."""
    program = f'{operator} {repr(operand)}\n'
    module = cs._parse_text(program)
    unaryop_node = list(module.nodes_of_class(astroid.UnaryOp))[0]
    assert unaryop_node.type_constraints.type == bool


if __name__ == '__main__':
    nose.main()
