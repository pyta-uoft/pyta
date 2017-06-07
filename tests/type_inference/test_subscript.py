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



@given(cs.binary_bool_operator, hs.lists(cs.primitive_values, min_size=2))
def test_homogeneous_binary_boolop(op, operand_list):
    """Test type setting of binary BoolOp node(s) representing expression with same binary boolean operations."""
    # get every permutation?
    assume(len(operand_list) > 0)
    pre_format_program = [repr(operand) for operand in operand_list]
    program = (' ' + op + ' ').join(pre_format_program)
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    operand_type = type(operand_list[0])
    homogeneous = True
    for operand in operand_list:
        if type(operand) != operand_type:
            homogeneous = False
            break
    if not homogeneous:
        expected_type = Any
    else:
        expected_type = operand_type
    assert boolop_node.type_constraints.type == expected_type


@given(hs.lists(cs.binary_bool_operator), hs.lists(cs.primitive_values))
def test_heterogeneous_binary_boolop(op_list, operand_list):
    """Test type setting of binary BoolOp node(s) representing expression with different binary boolean operations."""
    assume(len(op_list) > 0 and len(operand_list) == len(op_list) + 1)
    pre_format_program = [str(pair) if pair != '' else repr(pair) for operand_op_pair in zip(operand_list[:-1], op_list)
                          for pair in operand_op_pair]
    pre_format_program.append(repr(operand_list[-1]))
    program = ' '.join(pre_format_program)
    module = cs._parse_text(program)
    boolop_node = list(module.nodes_of_class(astroid.BoolOp))[0]
    operand_type = type(operand_list[0])
    homogeneous = True
    for operand in operand_list:
        if type(operand) != operand_type:
            homogeneous = False
            break
    if not homogeneous:
        expected_type = Any
    else:
        expected_type = operand_type
    assert boolop_node.type_constraints.type == expected_type



if __name__ == '__main__':
    nose.main()
