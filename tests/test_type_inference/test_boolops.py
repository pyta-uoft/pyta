import astroid

from pytest import skip
from hypothesis import given, settings, assume, HealthCheck
import hypothesis.strategies as hs
from .. import custom_hypothesis_support as cs
from typing import Any
settings.load_profile("pyta")


@given(cs.boolop_node(value=cs.const_node(hs.integers())))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_homogeneous_binary_boolop(node):
    """Test type setting of binary BoolOp node(s) representing expression with homogeneous operands."""
    module, _ = cs._parse_text(node)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    assert boolop_node.inf_type.getValue() == boolop_node.values[0].inf_type.getValue()


@given(cs.boolop_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_heterogeneous_binary_boolop(node):
    """Test type setting of binary BoolOp node(s) representing expression with heterogeneous operands."""
    skip('Currently fails due to typechecking for inheritance. '
                   'Need to figure out if this is expected behavior.')
    assume(type(node.values[0].value) != type(node.values[1].value))
    module, _ = cs._parse_text(node)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    assert boolop_node.inf_type.getValue() == Any
