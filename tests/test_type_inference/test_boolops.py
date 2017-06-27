import astroid
import nose
from hypothesis import given, settings, assume
import hypothesis.strategies as hs
import tests.custom_hypothesis_support as cs
from typing import Any
settings.load_profile("pyta")


@given(cs.boolop_node(value=cs.const_node(hs.integers())))
def test_homogeneous_binary_boolop(node):
    """Test type setting of binary BoolOp node(s) representing expression with homogeneous operands."""
    module, _ = cs._parse_text(node)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    assert boolop_node.type_constraints.type == boolop_node.values[0].type_constraints.type


@given(cs.boolop_node())
def test_heterogeneous_binary_boolop(node):
    """Test type setting of binary BoolOp node(s) representing expression with heterogeneous operands."""
    assume(type(node.values[0].value) != type(node.values[1].value))
    module, _ = cs._parse_text(node)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    assert boolop_node.type_constraints.type == Any


if __name__ == '__main__':
    nose.main()
