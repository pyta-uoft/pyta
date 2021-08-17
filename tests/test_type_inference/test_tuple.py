from typing import Tuple

import astroid
from hypothesis import HealthCheck, given, settings

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


@given(cs.tuple_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_tuple(t_tuple):
    """Test Tuple nodes representing a tuple of various types."""
    module, _ = cs._parse_text(t_tuple)
    for t_node in module.nodes_of_class(astroid.Tuple):
        elt_types = tuple(elt.inf_type.getValue() for elt in t_node.elts)
        assert t_node.inf_type.getValue() == Tuple[elt_types]
