import astroid
import nose
from hypothesis import assume, given, settings
import tests.custom_hypothesis_support as cs
from typing import Any, Dict, List, Tuple
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
    cs._verify_type_setting(module, astroid.List, List[type(lst.elts[0].value)])


@given(cs.list_node(min_size=2))
def test_random_lists(lst):
    """Test List nodes representing a list of values of different primitive types."""
    assume(not isinstance(lst.elts[0].value, type(lst.elts[1].value)))
    module, _ = cs._parse_text(lst)
    cs._verify_type_setting(module, astroid.List, List[Any])


@given(cs.simple_homogeneous_dict_node(min_size=1))
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    module, _ = cs._parse_text(dictionary)
    first_key, first_value = next(((k, v) for k, v in dictionary.items))
    cs._verify_type_setting(module, astroid.Dict, Dict[type(first_key.value), type(first_value.value)])


@given(cs.dict_node(min_size=2))
def test_heterogeneous_dict(node):
    """Test Dictionary nodes representing a dictionary with some key:value pairs of different types."""
    keys = [item.value for item, _ in node.items]
    values = [item.value for item, _ in node.items]
    assume(not isinstance(keys[0], type(keys[1])))
    assume(not isinstance(values[0], type(values[1])))
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
