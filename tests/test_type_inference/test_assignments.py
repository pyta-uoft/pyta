import astroid
import nose
from hypothesis import given, assume, settings, HealthCheck
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import TypeVar, Any
from keyword import iskeyword
settings.load_profile("pyta")


@given(cs.random_dict_variable_homogeneous_value(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_env(variables_dict):
    """Test environment setting visitors"""
    program = cs._parse_dictionary_to_program(variables_dict)
    module, _ = cs._parse_text(program)
    # get list of variable names in locals
    local_values = [module.type_environment.locals[name] for name in module.type_environment.locals]
    global_values = [module.type_environment.globals[name] for name in module.type_environment.globals]
    # verify the type of the value of each variable in the environment
    for value in local_values:
        assert isinstance(value, TypeVar)
    for value in global_values:
        assert isinstance(value, TypeVar)


@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1))
def test_set_name_unassigned(variable_name):
    """Test visitor for name nodes representing a single unassigned variable in module."""
    program = variable_name
    module, _ = cs._parse_text(program)
    for name_node in module.nodes_of_class(astroid.Name):
        name_type_var = name_node.frame().type_environment.lookup_in_env(name_node.name)
        assert name_node.type_constraints.type == name_type_var


@given(cs.random_dict_variable_homogeneous_value(min_size=1))
def test_set_name_assigned(variables_dict):
    """Test visitor for name nodes representing a variables with assigned values in module."""
    program = cs._parse_dictionary_to_program(variables_dict)
    for variable_name in variables_dict:
        program += variable_name + "\n"
    module, _ = cs._parse_text(program)
    for name_node in module.nodes_of_class(astroid.Name):
        name_type_var = name_node.frame().type_environment.lookup_in_env(name_node.name)
        assert name_node.type_constraints.type == name_type_var


@given(cs.random_dict_variable_homogeneous_value(min_size=1))
def test_set_single_assign(variables_dict):
    """Test single-target assignment statements; verify unification of type variables."""
    program = cs._parse_dictionary_to_program(variables_dict)
    module, inferer = cs._parse_text(program)
    for node in module.nodes_of_class(astroid.AssignName):
        target_name = node.name
        target_value = node.parent.value
        # lookup name in the frame's environment
        target_type_var = node.frame().type_environment.lookup_in_env(target_name)
        # do a concrete look up of the corresponding TypeVar
        target_type = inferer.type_constraints.lookup_concrete(target_type_var)
        # compare it to the type of the assigned value
        assert target_value.type_constraints.type == target_type


@given(cs.random_dict_variable_homogeneous_value(min_size=2))
def test_multi_target_assign(variables_dict):
    """Test multi-target assignment statements; verify unification of type variables."""
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
    program = (", ".join(variables_dict.keys())
        + " = "
        + ", ".join([repr(value) for value in variables_dict.values()]))
    module, inferer = cs._parse_text(program)
    # for each Assign node in program, verify unification of the type variables.
    for node in module.nodes_of_class(astroid.Assign):
        target_type_tuple = zip(node.targets[0].elts, node.value.elts)
        for target, value in target_type_tuple:
            target_type_var = target.frame().type_environment.lookup_in_env(target.name)
            assert inferer.type_constraints.lookup_concrete(target_type_var) == value.type_constraints.type


@given(hs.lists(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1), min_size=1), cs.primitive_values)
def test_set_multi_assign(variables_list, value):
    """Test environment setting visitors"""
    for variable_name in variables_list:
        assume(not iskeyword(variable_name))
    variables_list.append(repr(value))
    program = (" = ").join(variables_list)
    module, inferer = cs._parse_text(program)
    for target_node in module.nodes_of_class(astroid.AssignName):
        value_type = target_node.parent.value.type_constraints.type
        target_type_var = target_node.frame().type_environment.lookup_in_env(target_node.name)
        assert inferer.type_constraints.lookup_concrete(target_type_var) == value_type


@given(cs.random_dict_variable_homogeneous_value(min_size=2))
def test_assign_complex_homogeneous(variables_dict):
    """test whether visitors properly set the type constraint of the a assign node representing a multi-target-assign
     with a homogeneous list as the value.
    """
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
    program = ("x = ["
               + ", ".join([repr(value) for value in variables_dict.values()])
               + "]\n"
               + ", ".join(variables_dict.keys())
               + " = x")
    module, typeinferrer = cs._parse_text(program)
    ass_node = list(module.nodes_of_class(astroid.Assign))[0]
    for variable_name in variables_dict:
        var_tvar = module.type_environment.lookup_in_env(variable_name)
        assert typeinferrer.type_constraints.lookup_concrete(var_tvar) == ass_node.value.elts[0].type_constraints.type


@given(hs.lists(cs.valid_identifier(), min_size=2), cs.random_list(min_size=2))
def test_assign_complex(variables, values):
    """Test whether visitors properly set the type constraint of the a Assign node representing a multi-target-assign
     with a homogeneous list as the value.
    """
    assume(type(values[0]) != type(values[1]) and len(variables) == len(values))
    val_types = [type(val) for val in values]
    if int in val_types:
        assume(bool not in val_types)
    if bool in val_types:
        assume(int not in val_types)
    program = ("x = ["
               + ", ".join([repr(val) for val in values])
               + "]\n"
               + ", ".join(variables)
               + " = x")
    module, TypeInferrer = cs._parse_text(program)
    for variable_name in variables:
        variable_type_var = module.type_environment.lookup_in_env(variable_name)
        assert TypeInferrer.type_constraints.lookup_concrete(variable_type_var) == Any


if __name__ == '__main__':
    nose.main()
