import astroid
import nose
from hypothesis import given, settings, assume
from typing import Any, List
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.homogeneous_list(min_size=1), hs.integers())
def test_inference_list_subscript(input_list, index):
    """Test whether visitor properly set the type constraint of Subscript node representing list-index access."""
    program = f'{input_list}[{index}]'
    module, _ = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    list_node = list(module.nodes_of_class(astroid.List))[0]
    assert subscript_node.type_constraints.type == list_node.elts[0].type_constraints.type


@given(cs.homogeneous_dictionary(min_size=1))
def test_inference_dict_subscript(input_dict):
    for index in input_dict:
        program = f'{repr(input_dict)}[{repr(index)}]'
        module, _ = cs._parse_text(program)
        subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
        dict_node = list(module.nodes_of_class(astroid.Dict))[0]
        assert subscript_node.type_constraints.type == dict_node.items[0][1].type_constraints.type


@given(cs.homogeneous_list(min_size=1), cs.random_slice_indices())
def test_subscript_homogeneous_list_slice(input_list, slice):
    """Test visitor of Subscript node representing slicing of homogeneous list."""
    input_slice = ':'.join([str(index) if index else '' for index in slice])
    program = f'{input_list}[{input_slice}]'
    module, _ = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[subscript_node.value.elts[0].type_constraints.type]


@given(cs.random_list(min_size=2), cs.random_slice_indices())
def test_subscript_heterogeneous_list_slice(input_list, slice):
    """Test visitor of Subscript node representing slicing of heterogeneous list."""
    assume(not isinstance(input_list[0], type(input_list[1])))
    input_slice = ':'.join([str(index) if index else '' for index in slice])
    program = f'{input_list}[{input_slice}]'
    module, _ = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[Any]


if __name__ == '__main__':
    nose.main()
