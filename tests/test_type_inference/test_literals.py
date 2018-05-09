import astroid
import nose
from hypothesis import assume, given, settings, HealthCheck
import tests.custom_hypothesis_support as cs
from typing import Any, Dict, List, Set, Tuple
settings.load_profile("pyta")


@given(cs.subscript_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_index(node):
    module, _ = cs._parse_text(node)
    for index_node in module.nodes_of_class(astroid.Index):
        assert index_node.inf_type.type == index_node.value.inf_type.type


@given(cs.expr_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_expr(expr):
    module, _ = cs._parse_text(expr)
    for expr_node in module.nodes_of_class(astroid.Expr):
        assert expr_node.inf_type.type == expr_node.value.inf_type.type


if __name__ == '__main__':
    nose.main()
