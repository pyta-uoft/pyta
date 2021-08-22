import sys

import pytest
from astroid import nodes
from hypothesis import HealthCheck, assume, given, settings

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


@given(cs.subscript_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_index(node):
    if sys.version_info >= (3, 9):
        pytest.skip("Index node is deprecated in Python 3.9")
    module, _ = cs._parse_text(node)
    for index_node in module.nodes_of_class(nodes.Index):
        assert index_node.inf_type.getValue() == index_node.value.inf_type.getValue()


@given(cs.expr_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_expr(expr):
    module, _ = cs._parse_text(expr)
    for expr_node in module.nodes_of_class(nodes.Expr):
        assert expr_node.inf_type.getValue() == expr_node.value.inf_type.getValue()
