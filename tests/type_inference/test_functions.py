import astroid
import nose
from hypothesis import assume, given
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Callable
from python_ta.transforms.type_inference_visitor import register_type_constraints_setter,\
    environment_transformer, TYPE_CONSTRAINTS
from keyword import iskeyword


def _parse_to_function(function_name, args_list, return_value):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):\n' \
           f'    return {return_value}'


@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1), cs.primitive_values)
def test_function_def_no_args(function_name, return_value):
    """Test FunctionDef node visitors representing function definitions with no parameters and primitive return val."""
    assume(not iskeyword(function_name))
    program = _parse_to_function(function_name, [], repr(return_value))
    module = cs._parse_text(program)
    function_type_var = module.type_environment.lookup_in_env(function_name)
    assert TYPE_CONSTRAINTS.lookup_concrete(function_type_var) == Callable[[], type(return_value)]


@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1), cs.primitive_values)
def test_function_def_call_no_args(function_name, return_value):
    """Test type setting in environment of a function call for a function with no parameters."""
    TYPE_CONSTRAINTS.clear_tvars()
    assume(not iskeyword(function_name))
    program = _parse_to_function(function_name, [], repr(return_value)) + "\n" + function_name + "()\n"
    module = cs._parse_text(program)
    # there should be a single Expr node in this program
    expr_node = next(module.nodes_of_class(astroid.Expr))
    assert expr_node.type_constraints.type == type(return_value)


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=1))
def test_function_def_args_simple_return(function_name, arguments):
    """Test FunctionDef node visitors representing function definitions with paramater(s); return one of its arguments."""
    # generate every possible function definition program of aforementioned form.
    for argument in arguments:
        program = _parse_to_function(function_name, arguments, argument)
        module = cs._parse_text(program)
        # get the functionDef node - there is only one in this test case.
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [TYPE_CONSTRAINTS.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = TYPE_CONSTRAINTS.lookup_concrete(function_type_var)
        actual_arg_types, actual_return_type = TYPE_CONSTRAINTS.types_in_callable(function_type)
        return_type_var = function_def_node.type_environment.lookup_in_env(argument)
        expected_return_type = TYPE_CONSTRAINTS.lookup_concrete(return_type_var)
        assert Callable[actual_arg_types, actual_return_type] == Callable[expected_arg_types, expected_return_type]


@given(cs.valid_identifier(), cs.random_dict_variable_value(min_size=1))
def test_function_def_args_simple_function_call(function_name, variables_dict):
    """Test setting f env for function call of function definitions with params that returns one of it's arguments."""
    assume(not iskeyword(function_name) and function_name not in variables_dict)
    # generate every possible function definition program of aforementioned form.
    for i in range(len(list(variables_dict.keys()))):
        return_value = list(variables_dict.keys())[i]
        arguments = ", ".join([repr(value) for value in variables_dict.values()])
        program = f'{_parse_to_function(function_name, list(variables_dict.keys()), return_value)}\n' \
                  f'{function_name}({arguments})'
        module = cs._parse_text(program)
        # get the Call node - there is only one in this test case.
        call_node = next(module.nodes_of_class(astroid.Call))
        function_call_type = call_node.type_constraints.type
        assert TYPE_CONSTRAINTS.lookup_concrete(function_call_type) == call_node.args[i].type_constraints.type


if __name__ == '__main__':
    nose.main()
