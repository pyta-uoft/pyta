import astroid
import nose
from hypothesis import given
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import TypeVar
from python_ta.transforms.type_inference_visitor import TYPE_CONSTRAINTS


@given(cs.random_dict_variable_value(min_size=1))
def test_set_env(variables_dict):
    """Test environment setting visitors"""
    program = cs._parse_dictionary_to_program(variables_dict)
    module = cs._parse_text(program)
    # get list of variable names in locals
    local_values = [module.type_environment.locals[name] for name in module.type_environment.locals]
    global_values = [module.type_environment.globals[name] for name in module.type_environment.globals]
    # verify the type of the value of each variable in the environment
    for value in local_values: assert isinstance(value, TypeVar)
    for value in global_values: assert isinstance(value, TypeVar)

@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1))
def test_set_name_unassigned(variable_name):
    """Test visitor for name nodes representing a single unassigned variable in module."""
    program = variable_name
    module = cs._parse_text(program)
    for name_node in module.nodes_of_class(astroid.Name):
        name_type_var = name_node.frame().type_environment.lookup_in_env(name_node.name)
        assert name_node.type_constraints.type == name_type_var


@given(cs.random_dict_variable_value(min_size=1))
def test_set_name_assigned(variables_dict):
    """Test visitor for name nodes representing a variables with assigned values in module."""
    program = cs._parse_dictionary_to_program(variables_dict)
    for variable_name in variables_dict:
        program += variable_name + "\n"
    module = cs._parse_text(program)
    for name_node in module.nodes_of_class(astroid.Name):
        name_type_var = name_node.frame().type_environment.lookup_in_env(name_node.name)
        assert name_node.type_constraints.type == name_type_var


@given(cs.random_dict_variable_value(min_size=1))
def test_set_single_assign(variables_dict):
    """Test single-target assignment statements; verify unification of type variables."""
    program = cs._parse_dictionary_to_program(variables_dict)
    module = cs._parse_text(program)
    for node in module.nodes_of_class(astroid.AssignName):
        target_name = node.name
        target_value = node.parent.value
        # lookup name in the frame's environment
        target_type_var = node.frame().type_environment.lookup_in_env(target_name)
        # do a concrete look up of the corresponding TypeVar
        target_type = TYPE_CONSTRAINTS.lookup_concrete(target_type_var)
        # compare it to the type of the assigned value
        assert target_value.type_constraints.type == target_type


if __name__ == '__main__':
    nose.main()
