import astroid

from hypothesis import assume, given, settings, HealthCheck
from .. import custom_hypothesis_support as cs
from typing import Any, Set
settings.load_profile("pyta")


@given(cs.simple_homogeneous_set_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_homogeneous_set(node):
    """Test Set nodes representing a set of homogeneous values."""
    module, _ = cs._parse_text(node)
    set_node = list(module.nodes_of_class(astroid.Set))[0]
    if len(set_node.elts) == 0:
        assert set_node.inf_type.getValue() == Set[Any]
    else:
        try:
            cs._verify_type_setting(module, astroid.Set, Set[type(set_node.elts[0].value)])
        except AttributeError:
            cs._verify_type_setting(module, astroid.Set, Set[type(set_node.elts[0].operand.value)])


@given(cs.set_node(min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_random_set(node):
    """Test Set nodes representing a set of heterogeneous values."""
    assume(not isinstance(list(node.elts)[0].value, type(list(node.elts)[1].value)))
    assume(not isinstance(list(node.elts)[1].value, type(list(node.elts)[0].value)))
    val_types = [type(val.value) for val in node.elts]
    if int in val_types:
        assume(bool not in val_types)
    if bool in val_types:
        assume(int not in val_types)
    module, _ = cs._parse_text(node)
    set_node = list(module.nodes_of_class(astroid.Set))[0]
    cs._verify_type_setting(module, astroid.Set, Set[Any])
