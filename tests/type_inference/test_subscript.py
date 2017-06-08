import astroid
import nose
from hypothesis import given, settings, assume
from typing import Any, List
import tests.custom_hypothesis_support as cs
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
    assume(not isinstance(input_list[0], type(input_list[1])))
    input_slice = ':'.join([str(index) if index else '' for index in slice])
    program = f'{input_list}[{input_slice}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == List[cs._type_of_list(input_list)]


if __name__ == '__main__':
    nose.main()
