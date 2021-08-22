from typing import Any, Dict, List

from astroid import nodes
from hypothesis import HealthCheck, assume, given, settings

from .. import custom_hypothesis_support as cs
from ..custom_hypothesis_support import lookup_type

settings.load_profile("pyta")


@given(cs.simple_homogeneous_dict_node(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    module, _ = cs._parse_text(dictionary)
    dict_node = list(module.nodes_of_class(nodes.Dict))[0]
    if len(dict_node.items) == 0:
        assert dict_node.inf_type.getValue() == Dict[Any, Any]
    else:
        first_key, first_value = next(((k, v) for k, v in dictionary.items))
        cs._verify_type_setting(
            module, nodes.Dict, Dict[type(first_key.value), type(first_value.value)]
        )


@given(cs.dict_node(min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow, HealthCheck.filter_too_much])
def test_heterogeneous_dict(node):
    """Test Dictionary nodes representing a dictionary with some key:value pairs of different types."""
    keys = [item.value for item, _ in node.items]
    values = [item.value for _, item in node.items]
    assume(not isinstance(keys[0], type(keys[1])))
    assume(not isinstance(values[0], type(values[1])))
    assume(not isinstance(keys[1], type(keys[0])))
    assume(not isinstance(values[1], type(values[0])))
    key_types = [type(key.value) for key, _ in node.items]
    val_types = [type(val.value) for _, val in node.items]
    if int in key_types:
        assume(bool not in val_types)
    if bool in key_types:
        assume(int not in val_types)
    module, _ = cs._parse_text(node)
    cs._verify_type_setting(module, nodes.Dict, Dict[Any, Any])


def test_sorted_dict():
    src = """
    dictionary = {'B': 2, 'A': 1}
    sorted_dict = sorted(dictionary)
    """
    module, ti = cs._parse_text(src)
    assign_node = list(module.nodes_of_class(nodes.AssignName))[1]
    t = lookup_type(ti, assign_node, assign_node.name)
    assert ti.type_constraints.resolve(t).getValue() == List[str]


def test_any_dict():
    src = """
    dictionary = {'B': 2, 'A': 1, '': 3}
    any_empty = any(dictionary)
    """
    module, ti = cs._parse_text(src)
    assign_node = list(module.nodes_of_class(nodes.AssignName))[1]
    t = lookup_type(ti, assign_node, assign_node.name)
    assert ti.type_constraints.resolve(t).getValue() == bool
