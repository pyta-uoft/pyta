import astroid
import nose
from hypothesis import assume, given
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Any, Dict, List, Tuple, TypeVar
from python_ta.transforms.type_inference_visitor import register_type_constraints_setter,\
    environment_transformer, TYPE_CONSTRAINTS
from keyword import iskeyword


@given(cs.primitive_values)
def test_simple_literal(const):
    """Test Const nodes representing int, bool, float, and None literal values."""
    assume(not isinstance(const, str))
    module = _parse_text(str(const))
    cs._verify_type_setting(module, astroid.Const, type(const))


@given(cs.tuple_strategy(min_size=2))
def test_tuple(t_tuple):
    """ Test Tuple nodes representing a tuple of various types."""
    module = _parse_text(str(t_tuple))
    cs._verify_type_setting(module, astroid.Tuple, Tuple[tuple(type(x) for x in t_tuple)])


@given(cs.homogeneous_list(min_size=2))
def test_homogeneous_lists(lst):
    """Test List nodes representing a list of values of the same primitive type."""
    module = _parse_text(str(lst))
    cs._verify_type_setting(module, astroid.List, List[type(lst[0])])


@given(cs.random_list(min_size=2))
def test_random_lists(lst):
    """Test List nodes representing a list of values of different primitive types."""
    assume(not isinstance(lst[0], type(lst[1])))
    module = _parse_text(str(lst))
    cs._verify_type_setting(module, astroid.List, List[Any])


@given(cs.homogeneous_dictionary(min_size=1))
def test_homogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with all key:value pairs of same types."""
    module = _parse_text(str(dictionary))
    cs._verify_type_setting(module, astroid.Dict, Dict[type(list(dictionary.keys())[0]), type(list(dictionary.values())[0])])


@given(cs.heterogeneous_dictionary(min_size=2))
def test_heterogeneous_dict(dictionary):
    """Test Dictionary nodes representing a dictionary with some key:value pairs of different types."""
    assume(not isinstance(list(dictionary.keys())[0], type(list(dictionary.keys())[1])))
    module = _parse_text(str(dictionary))
    cs._verify_type_setting(module, astroid.Dict, Dict[Any, Any])


@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz"), hs.integers())
def test_string_index(string_input, index):
    """Test index visitor representing a subscript for a string"""
    input_index = cs._index_input_formatter(string_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.tuple_strategy(min_size=1), hs.integers())
def test_tuple_index(tuple_input, index):
    """Test index visitor representing a subscript for a tuple"""
    input_index = cs._index_input_formatter(tuple_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.random_list(min_size=2), hs.integers())
def test_list_index(list_input, index):
    """Test index visitor representing a subscript a list"""
    input_index = cs._index_input_formatter(list_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.heterogeneous_dictionary(min_size=2), cs.index_values)
def test_dict_index(dict_input, index):
    """Test index visitor representing a subscript a dictionary"""
    input_index = cs._index_input_formatter(dict_input, index)
    module = _parse_text(input_index)
    cs._verify_type_setting(module, astroid.Index, type(index))


@given(cs.primitive_values)
def test_const_expr(expr):
    """Test visitor for expression node representing a constant"""
    module = _parse_text(repr(expr))
    cs._verify_node_value_typematch(module)


@given(cs.tuple_strategy(min_size=2))
def test_tuple_expr(expr):
    """Test visitor for expression node representing a tuple"""
    module = _parse_text(repr(expr))
    cs._verify_node_value_typematch(module)


@given(cs.random_list(min_size=2))
def test_list_expr(expr):
    """Test visitor for expression node representing a list"""
    module = _parse_text(repr(expr))
    cs._verify_node_value_typematch(module)


@given(cs.heterogeneous_dictionary(min_size=2))
def test_dict_expr(expr):
    """Test visitor for expression node representing a dictionary"""
    module = _parse_text(repr(expr))
    cs._verify_node_value_typematch(module)


@given(cs.random_dict_variable_value(min_size=1))
def test_set_env(variables_dict):
    """Test environment setting visitors"""
    program = cs._parse_dictionary_to_program(variables_dict)
    module = _parse_text(program)
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
    module = _parse_text(program)
    for name_node in module.nodes_of_class(astroid.Name):
        name_type_var = name_node.frame().type_environment.lookup_in_env(name_node.name)
        assert name_node.type_constraints.type == name_type_var


@given(cs.random_dict_variable_value(min_size=1))
def test_set_name_assigned(variables_dict):
    """Test visitor for name nodes representing a variables with assigned values in module."""
    program = cs._parse_dictionary_to_program(variables_dict)
    for variable_name in variables_dict:
        program += variable_name + "\n"
    module = _parse_text(program)
    for name_node in module.nodes_of_class(astroid.Name):
        name_type_var = name_node.frame().type_environment.lookup_in_env(name_node.name)
        assert name_node.type_constraints.type == name_type_var


@given(cs.random_dict_variable_value(min_size=1))
def test_set_single_assign(variables_dict):
    """Test single-target assignment statements; verify unification of type variables."""
    program = cs._parse_dictionary_to_program(variables_dict)
    module = _parse_text(program)
    for node in module.nodes_of_class(astroid.AssignName):
        target_name = node.name
        target_value = node.parent.value
        # lookup name in the frame's environment
        target_type_var = node.frame().type_environment.lookup_in_env(target_name)
        # do a concrete look up of the corresponding TypeVar
        target_type = TYPE_CONSTRAINTS.lookup_concrete(target_type_var)
        # compare it to the type of the assigned value
        assert target_value.type_constraints.type == target_type


@given(cs.random_dict_variable_value(min_size=2))
def test_multi_target_assign(variables_dict):
    """Test multi-target assignment statements; verify unification of type variables."""
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
    program = (", ".join(variables_dict.keys())
        + " = "
        + ", ".join([repr(value) for value in variables_dict.values()]))
    module = _parse_text(program)
    # for each Assign node in program, verify unification of the type variables.
    for node in module.nodes_of_class(astroid.Assign):
        target_type_tuple = zip(node.targets[0].elts, node.value.elts)
        for target, value in target_type_tuple:
            target_type_var = target.frame().type_environment.lookup_in_env(target.name)
            assert TYPE_CONSTRAINTS.lookup_concrete(target_type_var) == value.type_constraints.type


def _parse_text(source: str) -> astroid.Module:
    """Parse source code text and output an AST with type inference performed."""
    module = astroid.parse(source)
    environment_transformer().visit(module)
    register_type_constraints_setter().visit(module)
    return module


if __name__ == '__main__':
    nose.main()
