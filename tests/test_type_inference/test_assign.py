from keyword import iskeyword
from typing import Any, List, TypeVar

import hypothesis.strategies as hs
import pytest
from astroid import nodes
from hypothesis import HealthCheck, assume, given, settings
from pytest import skip

from python_ta.typecheck.base import TypeFail

from .. import custom_hypothesis_support as cs
from ..custom_hypothesis_support import lookup_type

settings.load_profile("pyta")


@given(cs.random_dict_variable_homogeneous_value(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_env(variables_dict):
    """Test environment setting visitors"""
    program = cs._parse_dictionary_to_program(variables_dict)
    module, _ = cs._parse_text(program)
    # get list of variable names in locals
    local_values = [module.type_environment.locals[name] for name in module.type_environment.locals]
    global_values = [
        module.type_environment.globals[name] for name in module.type_environment.globals
    ]
    # verify the type of the value of each variable in the environment
    for value in local_values:
        assert isinstance(value, TypeVar)
    for value in global_values:
        assert isinstance(value, TypeVar)


@given(cs.valid_identifier())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_name_unassigned(identifier):
    """Test visitor for name nodes representing a single unassigned variable in module."""
    program = identifier
    module, _ = cs._parse_text(program)
    for name_node in module.nodes_of_class(nodes.Name):
        assert isinstance(name_node.inf_type, TypeFail)


@given(cs.random_dict_variable_homogeneous_value(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_name_assigned(variables_dict):
    """Test visitor for name nodes representing a variables with assigned values in module."""
    program = cs._parse_dictionary_to_program(variables_dict)
    for variable_name in variables_dict:
        program += variable_name + "\n"
    module, inferer = cs._parse_text(program)
    for name_node in module.nodes_of_class(nodes.Name):
        name_type = lookup_type(inferer, name_node, name_node.name)
        assert name_node.inf_type.getValue() == name_type


@given(cs.random_dict_variable_homogeneous_value(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_single_assign(variables_dict):
    """Test single-target assignment statements; verify unification of type variables."""
    program = cs._parse_dictionary_to_program(variables_dict)
    module, inferer = cs._parse_text(program)
    for node in module.nodes_of_class(nodes.AssignName):
        target_value = node.parent.value
        target_type = lookup_type(inferer, node, node.name)
        # compare it to the type of the assigned value
        assert target_value.inf_type.getValue() == target_type


@given(cs.random_dict_variable_homogeneous_value(min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_multi_target_assign(variables_dict):
    """Test multi-target assignment statements; verify unification of type variables."""
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
    program = (
        ", ".join(variables_dict.keys())
        + " = "
        + ", ".join([repr(value) for value in variables_dict.values()])
    )
    module, inferer = cs._parse_text(program)
    # for each Assign node in program, verify unification of the type variables.
    for node in module.nodes_of_class(nodes.Assign):
        target_type_tuple = zip(node.targets[0].elts, node.value.elts)
        for target, value in target_type_tuple:
            target_type_var = target.frame().type_environment.lookup_in_env(target.name)
            assert (
                inferer.type_constraints.resolve(target_type_var).getValue()
                == value.inf_type.getValue()
            )


@given(
    hs.lists(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1), min_size=1),
    cs.primitive_values,
)
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_multi_assign(variables_list, value):
    """Test environment setting visitors"""
    for variable_name in variables_list:
        assume(not iskeyword(variable_name))
    variables_list.append(repr(value))
    program = (" = ").join(variables_list)
    module, inferer = cs._parse_text(program)
    for target_node in module.nodes_of_class(nodes.AssignName):
        value_type = target_node.parent.value.inf_type.getValue()
        target_type_var = target_node.frame().type_environment.lookup_in_env(target_node.name)
        assert inferer.type_constraints.resolve(target_type_var).getValue() == value_type


@given(cs.random_dict_variable_homogeneous_value(min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_assign_complex_homogeneous(variables_dict):
    """test whether visitors properly set the type constraint of the a assign node representing a multi-target-assign
    with a homogeneous list as the value.
    """
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
    program = (
        "x = ["
        + ", ".join([repr(value) for value in variables_dict.values()])
        + "]\n"
        + ", ".join(variables_dict.keys())
        + " = x"
    )
    module, typeinferrer = cs._parse_text(program)
    ass_node = list(module.nodes_of_class(nodes.Assign))[0]
    for variable_name in variables_dict:
        var_tvar = module.type_environment.lookup_in_env(variable_name)
        assert (
            typeinferrer.type_constraints.resolve(var_tvar).getValue()
            == ass_node.value.elts[0].inf_type.getValue()
        )


@pytest.mark.skip(reason="Not a test")
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
    program = (
        "x = [" + ", ".join([repr(val) for val in values]) + "]\n" + ", ".join(variables) + " = x"
    )
    module, TypeInferrer = cs._parse_text(program)
    for variable_name in variables:
        variable_type_var = module.type_environment.lookup_in_env(variable_name)
        assert TypeInferrer.type_constraints.resolve(variable_type_var).getValue() == Any


def test_attribute_reassign():
    """Test for correct type setting after a redundant assignment of an instance attribute."""
    program = (
        f"class Student:\n"
        f"    def __init__(self, name1):\n"
        f"        self.name = name1\n"
        f"        self.name = name1\n"
        f"\n"
    )
    module, inferer = cs._parse_text(program)
    functiondef_node = next(module.nodes_of_class(nodes.FunctionDef))
    actual_type = lookup_type(inferer, functiondef_node, "name")
    expected_type = lookup_type(inferer, functiondef_node, "name1")
    assert inferer.type_constraints.can_unify(actual_type, expected_type)


def test_assign_autoconvert():
    skip("TODO: make this test pass (currently a unification fail)")
    program = """
    x = 1
    x = x + 1.0
    """
    module, inferer = cs._parse_text(program, reset=True)
    x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ][0]
    assert inferer.type_constraints.resolve(x).getValue() == float


def test_augassign_simple_fallback():
    program = """
    x += 1
    """
    module, inferer = cs._parse_text(program, reset=True)
    x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ][0]
    assert inferer.type_constraints.resolve(x).getValue() == int


def test_augassign_subscript_target():
    program = """
    x = ['a', 'b', 'c']
    x[0] += 'd'
    y = x[0]
    """
    module, inferer = cs._parse_text(program, reset=True)
    x, y = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ]
    assert inferer.type_constraints.resolve(y).getValue() == str


def test_augassign_builtin():
    program = """
    x = [1,2,3]
    x += set([4,5,6])
    """
    module, inferer = cs._parse_text(program, reset=True)
    x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ][0]
    assert inferer.type_constraints.resolve(x).getValue() == List[int]


def test_augassign_builtin_autoconvert():
    skip("TODO: make this test pass (currently a unification fail)")
    program = """
    x = 1
    x += 1.0
    """
    module, inferer = cs._parse_text(program, reset=True)
    x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ][0]
    assert inferer.type_constraints.resolve(x).getValue() == float


def test_augassign_builtin_attribute_autoconvert():
    skip("TODO: make this test pass (currently a unification fail)")
    program = """
    class A:
        def __init__(self):
            self.x = 1

    self.x += 1.0
    """
    module, inferer = cs._parse_text(program, reset=True)
    x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignAttr)
    ][0]
    assert inferer.type_constraints.resolve(x).getValue() == float


def test_augassign_userdefn():
    skip("Support for attribute-based inference required for this test to pass")
    program = """
    class A:
        def __init__(self, val):
            self.val = val

        def __iadd__(self, other):
            return A(int(self.val + other.val))

        def __add__(self, other):
            return A(str(self.val + other.val))

    a = A(0)
    b = A(1)
    a += b
    x = a.val
    """
    module, inferer = cs._parse_text(program, reset=True)
    a, b, _, x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ][6:]
    assert inferer.type_constraints.resolve(x).getValue() == int


def test_augassign_userdefn_fallback():
    skip("Support for attribute-based inference required for this test to pass")
    program = """
    class A:
        def __init__(self, val):
            self.val = val

        def __add__(self, other):
            return A(int(self.val + other.val))

    a = A(0)
    b = A(1)
    a += b
    x = a.val
    """
    module, inferer = cs._parse_text(program, reset=True)
    a, b, _, x = [
        inferer.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)
    ][4:]
    assert inferer.type_constraints.resolve(x).getValue() == int


def test_augassign_userdefn_fail():
    program = """
    class A:
        def __init__(self, val):
            self.val = val

    a = A(0)
    b = A(1)
    a += b
    x = a.val
    """
    module, inferer = cs._parse_text(program, reset=True)
    for aug_node in module.nodes_of_class(nodes.AugAssign):
        assert isinstance(aug_node.inf_type, TypeFail)
