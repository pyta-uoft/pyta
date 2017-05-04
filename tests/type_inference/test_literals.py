import astroid
import nose
from hypothesis import assume, given
import hypothesis.strategies as hs
from typing import Any, Dict, List, Tuple

from python_ta.transforms.type_inference_visitor import register_type_constraints_setter, environment_transformer


PRIMITIVE_TYPES = hs.sampled_from([
    hs.integers,
    hs.booleans,
    lambda: hs.floats(allow_nan=False, allow_infinity=False),
    hs.none,
    hs.text,
])
PRIMITIVE_VALUES = PRIMITIVE_TYPES.flatmap(lambda s: s())

INDEX_TYPES = hs.sampled_from([
    hs.integers,
    lambda: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1),
])
INDEX_VALUES = INDEX_TYPES.flatmap(lambda s: s())


def _verify_type_setting(module, ast_class, expected_type):
    """Helper to verify nodes visited by type inference visitor of astroid class has been properly transformed."""
    result = [n.type_constraints.type for n in module.nodes_of_class(ast_class)]
    assert [expected_type] == result


@given(PRIMITIVE_VALUES)
def test_simple_literal(const):
    """Test Const nodes representing int, bool, float, and None literal values."""
    assume(not isinstance(const, str))
    module = _parse_text(str(const))
    _verify_type_setting(module, astroid.Const, type(const))


@given((hs.lists(PRIMITIVE_VALUES, min_size=1)).map(tuple))
def test_tuple(t_tuple):
    """ Test Tuple nodes representing a tuple of various types."""
    module = _parse_text(str(t_tuple))
    _verify_type_setting(module, astroid.Tuple, Tuple[tuple(type(x) for x in t_tuple)])


@given(PRIMITIVE_TYPES.flatmap(lambda s: hs.lists(s(), min_size=1)))
def test_homogeneous_lists(lst):
    """Test List nodes representing a list of values of the same primitive type."""
    module = _parse_text(str(lst))
    _verify_type_setting(module, astroid.List, List[type(lst[0])])


@given(hs.lists(PRIMITIVE_VALUES, min_size=2))
def test_heterogeneous_lists(lst):
    """Test List nodes representing a list of values of different primitive types."""
    assume(not isinstance(lst[0], type(lst[1])))
    module = _parse_text(str(lst))
    _verify_type_setting(module, astroid.List, List[Any])


@given(PRIMITIVE_TYPES.flatmap(lambda s: hs.dictionaries(s(), s(),  min_size=1)))
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    module = _parse_text(str(dictionary))
    _verify_type_setting(module, astroid.Dict, Dict[type(list(dictionary.keys())[0]), type(list(dictionary.values())[0])])


@given(hs.dictionaries(PRIMITIVE_VALUES, PRIMITIVE_VALUES, min_size=2))
def test_heterogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with some key:value pairs of different types."""
    assume(not isinstance(list(dictionary.keys())[0], type(list(dictionary.keys())[1])))
    module = _parse_text(str(dictionary))
    _verify_type_setting(module, astroid.Dict, Dict[Any, Any])


@hs.composite
def string_and_index(draw):
    xs = draw(INDEX_VALUES)
    i = draw(hs.integers(min_value=0, max_value=len(str(xs)) - 1))
    return [repr(xs)  + "[" + repr(i) + "]", i]
@given(string_and_index())
def test_string_index(index):
    """Test index visitor representing a subscript for a string"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


@hs.composite
def tuple_and_index(draw, elements=PRIMITIVE_VALUES):
    xs = draw(hs.tuples(elements, elements))
    i = draw(hs.integers())
    return [repr(xs) + "[" + repr(i) + "]", i]
@given(tuple_and_index())
def test_tuple_index(index):
    """Test index visitor representing a subscript for a tuple"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


@hs.composite
def list_and_index(draw, elements=PRIMITIVE_VALUES):
    xs = draw(hs.lists(elements, min_size=1))
    i = draw(hs.integers(min_value=0, max_value=len(xs) - 1))
    return [repr(xs) + "[" + repr(i) + "]", i]
@given(list_and_index())
def test_list_index(index):
    """Test index visitor representing a subscript a list"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


@hs.composite
def dict_and_index(draw, elements=PRIMITIVE_VALUES):
    xs = draw(hs.dictionaries(INDEX_VALUES, elements, min_size=1))
    i = draw(INDEX_VALUES)
    return [repr(xs) + "[" + repr(i) + "]", i]
@given(dict_and_index())
def test_dict_index(index):
    """Test index visitor representing a subscript a dictionary"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


@given(PRIMITIVE_VALUES)
def test_const_expr(expr):
    """Test visitor for expression node representing a constant"""
    module = _parse_text(repr(expr))
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type


@given((hs.lists(PRIMITIVE_VALUES, min_size=1)).map(tuple))
def test_tuple_expr(expr):
    """Test visitor for expression node representing a tuple"""
    module = _parse_text(repr(expr))
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type


@given(hs.lists(PRIMITIVE_VALUES, min_size=1))
def test_list_expr(expr):
    """Test visitor for expression node representing a list"""
    module = _parse_text(repr(expr))
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type


@given(hs.dictionaries(PRIMITIVE_VALUES, PRIMITIVE_VALUES, min_size=2))
def test_dict_expr(expr):
    """Test visitor for expression node representing a dictionary"""
    module = _parse_text(repr(expr))
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type


def _parse_text(source: str) -> astroid.Module:
    """Parse source code text and output an AST with type inference performed."""
    module = astroid.parse(source)
    environment_transformer().visit(module)
    register_type_constraints_setter().visit(module)
    return module


if __name__ == '__main__':
    nose.main()
