import astroid
import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.unaryop_node(cs.non_bool_unary_op, cs.const_node(cs.numeric_values)))
def test_unaryop_non_bool_concrete(node):
    """Test type setting of UnaryOp node(s) with non-boolean operand."""
    assume(not (node.op == '~' and isinstance(node.operand.value, float)))
    module, _ = cs._parse_text(node)
    unaryop_node = list(module.nodes_of_class(astroid.UnaryOp))[0]
    assert unaryop_node.type_constraints.type == unaryop_node.operand.type_constraints.type


@given(cs.unaryop_node(cs.unary_bool_operator))
def test_not_bool(node):
    """Test type setting of UnaryOp node representing boolean operation not."""
    module, _ = cs._parse_text(node)
    for unaryop_node in module.nodes_of_class(astroid.UnaryOp):
        if unaryop_node.op == 'not':
            assert unaryop_node.type_constraints.type == bool


if __name__ == '__main__':
    nose.main()
