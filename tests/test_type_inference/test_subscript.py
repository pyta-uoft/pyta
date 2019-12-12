import astroid

from pytest import skip
from hypothesis import given, settings, HealthCheck
from typing import List
from .. import custom_hypothesis_support as cs
from python_ta.typecheck.base import TypeFail, TypeFailFunction
from python_ta.transforms.type_inference_visitor import NoType
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


@given(cs.subscript_node(cs.simple_homogeneous_list_node(min_size=1), cs.slice_node()))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_subscript_load_ctx(node):
    """Test visitor of Subscript node when loaded in an (if) expression."""
    load_node = astroid.If()
    load_node.postinit(astroid.Const(True), [node], [])
    module, _ = cs._parse_text(load_node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        list_node = subscript_node.value
        assert subscript_node.inf_type.getValue() == List[list_node.elts[0].inf_type.getValue()]


def test_homogenous_list_store_ctx():
    """Test visitor of Subscript node within a homogenous list assignment."""
    program = \
        '''
        [1,2,3][0] = 2
        '''
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        assert assign_node.inf_type == NoType()
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        assert subscript_node.inf_type == NoType()


def test_homogenous_list_invalid_store_ctx():
    """Test visitor of Subscript node within an invalid homogenous list assignment."""
    program = \
        '''
        [1,2,3][0] = 'a'
        '''
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        assert subscript_node.inf_type == NoType()


@given(cs.subscript_node(cs.list_node(min_size=1), cs.slice_node()))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_subscript_del_ctx(node):
    """Test visitor of Subscript node within a del statement."""
    del_node = astroid.Delete()
    del_node.postinit([node])
    module, _ = cs._parse_text(del_node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        assert subscript_node.inf_type.getValue() == type(None)


@given(cs.simple_homogeneous_dict_node(min_size=1))
def test_inference_dict_subscript(node):
    """Note that this test only takes in a dictionary because the subscript index
    must be the same type as the dictionary's keys in order to type check.
    """
    for key, _ in node.items:
        new_node = astroid.Subscript()
        new_node.postinit(node, key)
        module, _ = cs._parse_text(new_node)
        for subscript_node in module.nodes_of_class(astroid.Subscript):
            dict_node = subscript_node.value
            assert subscript_node.inf_type.getValue() == list(dict_node.items)[0][1].inf_type.getValue()


@given(cs.simple_homogeneous_list_node(min_size=1))
def test_inference_invalid_slice(node):
    sub_node = astroid.Subscript()
    slice = astroid.Slice()
    slice.postinit(astroid.Const(0), astroid.Const('a'))
    sub_node.postinit(node, slice)
    module, _ = cs._parse_text(sub_node)
    for subscript_node in module.nodes_of_class(astroid.Subscript):
        assert isinstance(subscript_node.inf_type, TypeFail)


def test_inference_ext_slice():
    skip('Lookup for class methods must be implemeneted before this test can pass')
    program = \
        '''
        class Foo:
            def __getitem__(self, tup):
                return tup[0]
        
        foo = Foo()
        foo[1, 'a']
        '''
    module, _ = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[1]
    assert subscript_node.inf_type.getValue() == int


def test_subscript_slice():
    program = '''
        x = List[:]
        '''
    module, _ = cs._parse_text(program)
    assign_node = next(module.nodes_of_class(astroid.Assign))
    assert isinstance(assign_node.inf_type, TypeFail)


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
