import astroid
import nose
from hypothesis import assume, given, settings, HealthCheck
import tests.custom_hypothesis_support as cs
from typing import Any, List
settings.load_profile("pyta")


@given(cs.simple_homogeneous_list_node(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_homogeneous_lists(lst):
    """Test List nodes representing a list of values of the same primitive type."""
    module, _ = cs._parse_text(lst)
    list_node = list(module.nodes_of_class(astroid.List))[0]
    if len(list_node.elts) == 0:
        assert list_node.type_constraints.type == List[Any]
    else:
        cs._verify_type_setting(module, astroid.List, List[type(lst.elts[0].value)])


@given(cs.list_node(min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_random_lists(lst):
    """Test List nodes representing a list of values of different primitive types."""
    assume(not isinstance(lst.elts[0].value, type(lst.elts[1].value)))
    assume(not isinstance(lst.elts[1].value, type(lst.elts[0].value)))
    val_types = [type(val.value) for val in lst.elts]
    if int in val_types:
        assume(bool not in val_types)
    if bool in val_types:
        assume(int not in val_types)
    module, _ = cs._parse_text(lst)
    cs._verify_type_setting(module, astroid.List, List[Any])


if __name__ == '__main__':
    nose.main()
