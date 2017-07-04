import astroid
import nose
from hypothesis import assume, given, settings
import tests.custom_hypothesis_support as cs
from typing import Any, Dict, List, Set, Tuple
settings.load_profile("pyta")


@given(cs.const_node())
def test_simple_literal(node):
    """Test Const nodes representing int, bool, float, and None literal values."""
    assume(not(isinstance(node.value, str)))
    module, _ = cs._parse_text(node)
    cs._verify_type_setting(module, astroid.Const, type(node.value))


@given(cs.tuple_node())
def test_tuple(t_tuple):
    """ Test Tuple nodes representing a tuple of various types."""
    module, _ = cs._parse_text(t_tuple)
    for t_node in module.nodes_of_class(astroid.Tuple):
        elt_types = tuple(elt.type_constraints.type for elt in t_node.elts)
        assert t_node.type_constraints.type == Tuple[elt_types]


@given(cs.simple_homogeneous_list_node(min_size=1))
def test_homogeneous_lists(lst):
    """Test List nodes representing a list of values of the same primitive type."""
    module, _ = cs._parse_text(lst)
    list_node = list(module.nodes_of_class(astroid.List))[0]
    if len(list_node.elts) == 0:
        assert list_node.type_constraints.type == List[Any]
    else:
        cs._verify_type_setting(module, astroid.List, List[type(lst.elts[0].value)])


@given(cs.list_node(min_size=2))
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


@given(cs.simple_homogeneous_set_node())
def test_homogeneous_set(node):
    """Test Set nodes representing a set of homogeneous values."""
    module, _ = cs._parse_text(node)
    set_node = list(module.nodes_of_class(astroid.Set))[0]
    if len(set_node.elts) == 0:
        assert set_node.type_constraints.type == Set[Any]
    else:
        try:
            cs._verify_type_setting(module, astroid.Set, Set[type(set_node.elts[0].value)])
        except AttributeError:
            cs._verify_type_setting(module, astroid.Set, Set[type(set_node.elts[0].operand.value)])


@given(cs.set_node(min_size=2))
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


@given(cs.simple_homogeneous_dict_node(min_size=1))
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    module, _ = cs._parse_text(dictionary)
    dict_node = list(module.nodes_of_class(astroid.Dict))[0]
    if len(dict_node.items) == 0:
        assert dict_node.type_constraints.type == Dict[Any, Any]
    else:
        first_key, first_value = next(((k, v) for k, v in dictionary.items))
        cs._verify_type_setting(module, astroid.Dict, Dict[type(first_key.value), type(first_value.value)])


@given(cs.dict_node(min_size=2))
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
    cs._verify_type_setting(module, astroid.Dict, Dict[Any, Any])


@given(cs.subscript_node())
def test_index(node):
    module, _ = cs._parse_text(node)
    for index_node in module.nodes_of_class(astroid.Index):
        assert index_node.type_constraints.type == index_node.value.type_constraints.type


@given(cs.expr_node())
def test_expr(expr):
    module, _ = cs._parse_text(expr)
    for expr_node in module.nodes_of_class(astroid.Expr):
        assert expr_node.type_constraints.type == expr_node.value.type_constraints.type


if __name__ == '__main__':
    nose.main()
