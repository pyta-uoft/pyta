from astroid import nodes
from hypothesis import HealthCheck, assume, given, settings

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


@given(cs.unaryop_node(cs.non_bool_unary_op, cs.const_node(cs.numeric_values)))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_unaryop_non_bool_concrete(node):
    """Test type setting of UnaryOp node(s) with non-boolean operand."""
    assume(not (node.op == "~" and isinstance(node.operand.value, float)))
    module, _ = cs._parse_text(node)
    unaryop_node = list(module.nodes_of_class(nodes.UnaryOp))[0]
    assert unaryop_node.inf_type.getValue() == unaryop_node.operand.inf_type.getValue()


@given(cs.unaryop_node(cs.unary_bool_operator))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_not_bool(node):
    """Test type setting of UnaryOp node representing boolean operation not."""
    module, _ = cs._parse_text(node)
    for unaryop_node in module.nodes_of_class(nodes.UnaryOp):
        if unaryop_node.op == "not":
            assert unaryop_node.inf_type.getValue() == bool
