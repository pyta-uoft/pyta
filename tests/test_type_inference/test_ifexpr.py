from typing import Any

from astroid import nodes
from hypothesis import HealthCheck, given, settings

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


@given(cs.ifexp_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_ifexp(node):
    """Test the type setting of an IfExp node representing an if statement."""
    module, type_inferer = cs._parse_text(node)
    for ifexp_node in module.nodes_of_class(nodes.IfExp):
        assert ifexp_node.inf_type.getValue() == ifexp_node.body.inf_type.getValue()
