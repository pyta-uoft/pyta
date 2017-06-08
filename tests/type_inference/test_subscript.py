import astroid
import nose
from hypothesis import given, settings, assume
from typing import Any, List
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.homogeneous_list(min_size=1), cs.random_slice_indices())
def test_subscript_homogeneous_list_slice(input_list, slice):
    """Test visitor of Subscript node representing slicing of homogeneous list."""
    input_slice = ':'.join([str(index) if index else '' for index in slice])
    program = f'{input_list}[{input_slice}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[cs._type_of_list(input_list)]


@given(cs.random_list(min_size=1), cs.random_slice_indices())
def test_subscript_heterogeneous_list_slice(input_list, slice):
    """Test visitor of Subscript node representing slicing of heterogeneous list."""
    input_slice = ':'.join([str(index) if index else '' for index in slice])
    program = f'{input_list}[{input_slice}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[cs._type_of_list(input_list)]


@given(cs.homogeneous_list(min_size=1), hs.integers())
def test_inference_list_subscript(input_list, index):
    """Test whether visitor properly set the type constraint of Subscript node representing list-index access."""
    program = f'{input_list}[{index}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == type(input_list[0])


@given(cs.random_dict_variable_value(min_size=1))
def test_inference_dict_subscript(input_dict):
    for index in input_dict:
        program = f'{input_dict}[{index}]'
        module = cs._parse_text(program)
        subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
        assert subscript_node.type_constraints.type == type(input_dict[index])


@given(cs.random_list(min_size=1), hs.integers())
def test_subscript_lower_slice_random(input_list, index):
    """Test type constraint of Subscript node representing a lower-slice of random list."""
    assume(len(input_list) > index)
    program = f'{input_list}[:{index}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[cs._type_of_list(input_list)]


@given(cs.homogeneous_list(min_size=1), hs.integers())
def test_subscript_lower_slice_homogeneous(input_list, index):
    """Test type constraint of Subscript node representing a lower-slice of homogeneous list."""
    assume(len(input_list) > index)
    program = f'{input_list}[:{index}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[type(input_list[0])]


@given(cs.random_list(min_size=1), hs.integers(), hs.integers())
def test_subscript_full_slice_random(input_list, index1, index2):
    """Test type constraint of Subscript node representing a full-slice of random list."""
    assume(len(input_list) > index2 > index1)
    program = f'{input_list}[{index1}:{index2}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    a = subscript_node.type_constraints.type
    assert subscript_node.type_constraints.type == List[cs._type_of_list(input_list)]


@given(cs.homogeneous_list(min_size=1), hs.integers(), hs.integers())
def test_subscript_full_slice_homogeneous(input_list, index1, index2):
    """Test type constraint of Subscript node representing a full-slice of homogeneous list."""
    assume(len(input_list) > index2 > index1)
    program = f'{input_list}[{index1}:{index2}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[type(input_list[0])]


@given(cs.random_list(min_size=1), hs.integers())
def test_subscript_upper_slice_random(input_list, index):
    """Test type constraint of Subscript node representing a upper-slice of random list."""
    assume(len(input_list) > index)
    program = f'{input_list}[{index}:]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[cs._type_of_list(input_list)]


@given(cs.homogeneous_list(min_size=1), hs.integers())
def test_subscript_upper_slice_homogeneous(input_list, index):
    """Test type constraint of Subscript node representing a upper-slice of homogeneous list."""
    assume(len(input_list) > index)
    program = f'{input_list}[{index}:]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[type(input_list[0])]


if __name__ == '__main__':
    nose.main()
