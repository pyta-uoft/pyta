import astroid
import nose
from nose import SkipTest
from python_ta.typecheck.base import TypeFail
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
        assert list_node.inf_type.getValue() == List[Any]
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


def test_empty_list_reassign():
    src = """
    x = []
    x = [1]
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == List[int]


def test_empty_list_reassign_twice():
    raise SkipTest('This test requires special treatment of Any in generics')
    src = """
    x = []
    x = [1]
    x = [1, 'abc']
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == List[Any]


def test_empty_list_append():
    src = """
    x = []
    x.append(1)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == List[int]


def test_empty_list_append_invalid():
    raise SkipTest('This test requires special treatment of Any in generics')
    src = """
    x = []
    x.append(1)
    x.append('abc')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert isinstance(ti.type_constraints.resolve(x), TypeFail)


def test_list_append():
    src = """
    x = [1,2,3]
    x.append(4)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == List[int]


if __name__ == '__main__':
    nose.main()
