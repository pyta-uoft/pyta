import astroid
import nose
from hypothesis import assume, given
import tests.custom_hypothesis_support as cs
from typing import Any, Dict, List, Tuple

from python_ta.transforms.type_inference_visitor import register_type_constraints_setter, environment_transformer


@given(cs.primitive_values)
def test_simple_literal(const):
    """Test Const nodes representing int, bool, float, and None literal values."""
    assume(not isinstance(const, str))
    module = _parse_text(str(const))
    cs._verify_type_setting(module, astroid.Const, type(const))


@given(cs.tuple_strategy(min_size=2))
def test_tuple(t_tuple):
    """ Test Tuple nodes representing a tuple of various types."""
    module = _parse_text(str(t_tuple))
    cs._verify_type_setting(module, astroid.Tuple, Tuple[tuple(type(x) for x in t_tuple)])


@given(cs.homogeneous_list(min_size=2))
def test_homogeneous_lists(lst):
    """Test List nodes representing a list of values of the same primitive type."""
    module = _parse_text(str(lst))
    cs._verify_type_setting(module, astroid.List, List[type(lst[0])])


@given(cs.random_list(min_size=2))
def test_random_lists(lst):
    """Test List nodes representing a list of values of different primitive types."""
    assume(not isinstance(lst[0], type(lst[1])))
    module = _parse_text(str(lst))
    cs._verify_type_setting(module, astroid.List, List[Any])


@given(cs.homogeneous_dictionary)
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    module = _parse_text(str(dictionary))
    cs._verify_type_setting(module, astroid.Dict, Dict[type(list(dictionary.keys())[0]), type(list(dictionary.values())[0])])


@given(cs.heterogeneous_dictionary)
def test_heterogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with some key:value pairs of different types."""
    assume(not isinstance(list(dictionary.keys())[0], type(list(dictionary.keys())[1])))
    module = _parse_text(str(dictionary))
    cs._verify_type_setting(module, astroid.Dict, Dict[Any, Any])


@given(cs.string(min_size=1), cs.integer)
def test_string_index(string_input, index):
    """Test index visitor representing a subscript for a string"""
    input_index = cs._index_input_formatter(string_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.tuple_strategy(min_size=1), cs.integer)
def test_tuple_index(tuple_input, index):
    """Test index visitor representing a subscript for a tuple"""
    input_index = cs._index_input_formatter(tuple_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.random_list(min_size=2), cs.integer)
def test_list_index(list_input, index):
    """Test index visitor representing a subscript a list"""
    input_index = cs._index_input_formatter(list_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.heterogeneous_dictionary, cs.index_values)
def test_dict_index(dict_input, index):
    """Test index visitor representing a subscript a dictionary"""
    input_index = cs._index_input_formatter(dict_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.primitive_values)
def test_const_expr(expr):
    """Test visitor for expression node representing a constant"""
    module = _parse_text(repr(expr))
    cs._verify_type_inf_child(module)


@given(cs.tuple_strategy(min_size=2))
def test_tuple_expr(expr):
    """Test visitor for expression node representing a tuple"""
    module = _parse_text(repr(expr))
    cs._verify_type_inf_child(module)


@given(cs.random_list(min_size=2))
def test_list_expr(expr):
    """Test visitor for expression node representing a list"""
    module = _parse_text(repr(expr))
    cs._verify_type_inf_child(module)


@given(cs.heterogeneous_dictionary)
def test_dict_expr(expr):
    """Test visitor for expression node representing a dictionary"""
    module = _parse_text(repr(expr))
    cs._verify_type_inf_child(module)


def _parse_text(source: str) -> astroid.Module:
    """Parse source code text and output an AST with type inference performed."""
    module = astroid.parse(source)
    environment_transformer().visit(module)
    register_type_constraints_setter().visit(module)
    return module


def test_local_env():
    """Test local environment nodes representing local environment variables"""
    module = _parse_text("ryan = 1\nryan")
    cs._verify_type_setting(module, astroid.Const, type(1))


if __name__ == '__main__':
    nose.main()
