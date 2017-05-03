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
    hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1),
])
INDEX_VALUES = INDEX_TYPES.flatmap(lambda s: s())


@given(PRIMITIVE_VALUES)
def test_simple_literal(const):
    """Test Const nodes representing int, bool, float, and None literal values."""
    assume(not isinstance(const, str))
    module = _parse_text(str(const))
    result = [n.type_constraints.type for n in module.nodes_of_class(
        astroid.Const)]
    assert [type(const)] == result


@given((hs.lists(PRIMITIVE_VALUES, min_size=1)).map(tuple))
def test_tuple(t_tuple):
    """ Test Tuple nodes representing a tuple of various types."""
    module = _parse_text(str(t_tuple))
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Tuple)]
    assert [Tuple[tuple(type(x) for x in t_tuple)]] == result


@given(PRIMITIVE_TYPES.flatmap(lambda s: hs.lists(s(), min_size=1)))
def test_homogeneous_lists(lst):
    """Test List nodes representing a list of values of the same primitive type."""
    module = _parse_text(str(lst))
    result = [n.type_constraints.type for n in module.nodes_of_class(
        astroid.List)]
    assert [List[type(lst[0])]] == result


@given(hs.lists(PRIMITIVE_VALUES, min_size=2))
def test_heterogeneous_lists(lst):
    """Test List nodes representing a list of values of different primitive types."""
    assume(not isinstance(lst[0], type(lst[1])))

    module = _parse_text(str(lst))
    result = [n.type_constraints.type for n in module.nodes_of_class(
        astroid.List)]
    assert [List[Any]] == result


@given(PRIMITIVE_TYPES.flatmap(lambda s: hs.dictionaries(s(), s(),  min_size=1)))
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    # first turn the raw input into a program in order to parse into an AST "module"
    # module should have been properly transformed using type_inference_visitor methods
    module = _parse_text(str(dictionary))
    # iterate through nodes of AST that are of class Dictionary and instantiate corresponding list of types
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Dict)]
    # get list of types
    assert [Dict[type(list(dictionary.keys())[0]), type(list(dictionary.values())[0])]] == result


@given(hs.dictionaries(PRIMITIVE_VALUES, PRIMITIVE_VALUES, min_size=2))
def test_heterogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with some key:value pairs of different types."""
    assume(not isinstance(list(dictionary.keys())[0], type(list(dictionary.keys())[1])))
    module = _parse_text(str(dictionary))
    # iterate through nodes of AST that are of class Dictionary and instantiate corresponding list of types
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Dict)]
    # get list of types
    assert [Dict[Any, Any]] == result


@hs.composite
def string_and_index(draw):
    xs = draw(INDEX_TYPES)
    i = draw(hs.integers(min_value=0, max_value=len(str(xs)) - 1))
    return ["\"" +str(xs) + "\"" + "[" + str(i) + "]", i]
@given(string_and_index())
def test_string_index(index):
    """Test index nodes representing a subscript"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


@hs.composite
def tuple_and_index(draw, elements=PRIMITIVE_VALUES):
    xs = draw(hs.tuples(elements, elements))
    i = draw(hs.integers(min_value=0, max_value=1))
    return [str(xs) + "[" + str(i) + "]", i]
@given(tuple_and_index())
def test_tuple_index(index):
    """Test index nodes representing a subscript"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


@hs.composite
def list_and_index(draw, elements=PRIMITIVE_VALUES):
    xs = draw(hs.lists(elements, min_size=1))
    i = draw(hs.integers(min_value=0, max_value=len(xs) - 1))
    return [str(xs) + "[" + str(i) + "]", i]
@given(list_and_index())
def test_list_index(index):
    """Test index nodes representing a subscript"""
    module = _parse_text(index[0])
    result = [n.type_constraints.type for n in module.nodes_of_class(astroid.Index)]
    assert [type(index[1])] == result


def _parse_text(source: str) -> astroid.Module:
    """Parse source code text and output an AST with type inference performed."""
    module = astroid.parse(source)
    environment_transformer().visit(module)
    register_type_constraints_setter().visit(module)
    return module


if __name__ == '__main__':
    nose.main()
