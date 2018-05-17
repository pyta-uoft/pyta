import astroid
import nose
from hypothesis import given, settings, HealthCheck
from typing import List
import tests.custom_hypothesis_support as cs
from python_ta.typecheck.base import TypeFail
settings.load_profile("pyta")


@given(cs.subscript_node(cs.simple_homogeneous_list_node(min_size=1), cs.index_node()))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_inference_list_subscript(node):
    """Test whether visitor properly set the type constraint of Subscript node representing list-index access."""
    module, _ = cs._parse_text(node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        list_node = subscript_node.value
        assert subscript_node.inf_type.getValue() == list_node.elts[0].inf_type.getValue()


@given(cs.subscript_node(cs.simple_homogeneous_list_node(min_size=1), cs.slice_node()))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_subscript_homogeneous_list_slice(node):
    """Test visitor of Subscript node representing slicing of homogeneous list."""
    module, _ = cs._parse_text(node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        list_node = subscript_node.value
        assert subscript_node.inf_type.getValue() == List[list_node.elts[0].inf_type.getValue()]


# TODO: this test currently fails
# @given(cs.simple_homogeneous_dict_node(min_size=1))
# def test_inference_dict_subscript(node):
#     """Note that this test only takes in a dictionary because the subscript index
#     must be the same type as the dictionary's keys in order to type check.
#     """
#     for key, _ in node.items:
#         new_node = astroid.Subscript()
#         new_node.postinit(node, key)
#         module, _ = cs._parse_text(new_node)
#         for subscript_node in module.nodes_of_class(astroid.Subscript):
#             dict_node = subscript_node.value
#             assert subscript_node.inf_type.getValue() == list(dict_node.items)[0][1].inf_type. getValue()


@given(cs.simple_homogeneous_list_node(min_size=1))
def test_inference_invalid_slice(node):
    sub_node = astroid.Subscript()
    slice = astroid.Slice()
    slice.postinit(astroid.Const(0), astroid.Const('a'))
    sub_node.postinit(node, slice)
    module, _ = cs._parse_text(sub_node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        assert isinstance(subscript_node.inf_type, TypeFail)


@given(cs.simple_homogeneous_list_node(min_size=1))
def test_inference_invalid_ext_slice(node):
    sub_node = astroid.Subscript()
    slice1 = astroid.Slice()
    slice1.postinit(astroid.Const(0), astroid.Const(1))
    slice2 = 'a'
    ext_slice = astroid.ExtSlice()
    ext_slice.postinit([slice1, slice2])
    sub_node.postinit(node, ext_slice)
    module, _ = cs._parse_text(sub_node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        assert isinstance(subscript_node.inf_type, TypeFail)


# TODO: this test needs to be converted, but will also fail
# @given(cs.random_list(min_size=2), cs.random_slice_indices())
# def test_subscript_heterogeneous_list_slice(input_list, slice):
#     """Test visitor of Subscript node representing slicing of heterogeneous list."""
#     assume(not isinstance(input_list[0], type(input_list[1])))
#     input_slice = ':'.join([str(index) if index else '' for index in slice])
#     program = f'{input_list}[{input_slice}]'
#     module, _ = cs._parse_text(program)
#     subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
#     assert subscript_node.inf_type.getValue() == List[Any]


if __name__ == '__main__':
    nose.main()
