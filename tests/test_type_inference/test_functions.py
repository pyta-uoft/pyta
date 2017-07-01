import astroid
import nose
from hypothesis import assume, given, settings
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Callable
from keyword import iskeyword
settings.load_profile("pyta")


def _parse_to_function(function_name, args_list, return_statement):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):' \
           f'    return {return_statement}'


def _parse_to_function_no_return(function_name, args_list, function_body):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):\n' \
           f'    {function_body}'


@given(cs.valid_identifier(), cs.primitive_values)
def test_function_def_no_args(function_name, return_value):
    """Test FunctionDef node visitors representing function definitions with no parameters and primitive return type."""
    assume(not iskeyword(function_name))
    program = _parse_to_function(function_name, [], repr(return_value))
    module, inferer = cs._parse_text(program)
    function_type_var = module.type_environment.lookup_in_env(function_name)
    function_def_node = list(module.nodes_of_class(astroid.FunctionDef))[0]
    return_tvar = function_def_node.type_environment.lookup_in_env('return')
    return_type = inferer.type_constraints.lookup_concrete(return_tvar)
    assert inferer.type_constraints.lookup_concrete(function_type_var) == Callable[[], return_type]


@given(cs.valid_identifier(), cs.primitive_values)
def test_function_def_call_no_args(function_name, return_value):
    """Test type setting in environment of a function call for a function with no parameters."""
    program = _parse_to_function(function_name, [], repr(return_value)) + "\n" + function_name + "()\n"
    module, inferer = cs._parse_text(program)
    # there should be a single Expr node in this program
    function_def_node = list(module.nodes_of_class(astroid.FunctionDef))[0]
    return_tvar = function_def_node.type_environment.lookup_in_env('return')
    return_type = inferer.type_constraints.lookup_concrete(return_tvar)
    expr_node = next(module.nodes_of_class(astroid.Expr))
    assert expr_node.type_constraints.type == return_type


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=0), cs.primitive_values)
def test_function_def_no_return(function_name, arguments, body):
    """Test FunctionDef node visitors representing non-returning function definitions with parameter(s)."""
    for return_value in ['return None', repr(body), 'pass']:
        program = _parse_to_function_no_return(function_name, arguments, repr(return_value))
        module, inferer = cs._parse_text(program)
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        assert inferer.type_constraints.lookup_concrete(function_type_var) == Callable[expected_arg_types, None]


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=1))
def test_function_def_args_simple_return(function_name, arguments):
    """Test FunctionDef node visitors representing function definitions with paramater(s):
     return one of its arguments."""
    for argument in arguments:
        program = _parse_to_function(function_name, arguments, argument)
        module, inferer = cs._parse_text(program)
        # get the functionDef node - there is only one in this test case.
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = inferer.type_constraints.lookup_concrete(function_type_var)
        actual_arg_types, actual_return_type = inferer.type_constraints.types_in_callable(function_type)
        return_type_var = function_def_node.type_environment.lookup_in_env(argument)
        expected_return_type = inferer.type_constraints.lookup_concrete(return_type_var)
        assert Callable[actual_arg_types, actual_return_type] == Callable[expected_arg_types, expected_return_type]


@given(cs.valid_identifier(), cs.random_dict_variable_homogeneous_value(min_size=1))
def test_function_def_args_simple_function_call(function_name, variables_dict):
    """Test setting f env for function call of function definitions with params that returns one of it's arguments."""
    assume(not iskeyword(function_name) and function_name not in variables_dict)
    # generate every possible function definition program of aforementioned form.
    for i in range(len(list(variables_dict.keys()))):
        return_value = list(variables_dict.keys())[i]
        arguments = ", ".join([repr(value) for value in variables_dict.values()])
        program = f'{_parse_to_function(function_name, list(variables_dict.keys()), return_value)}\n' \
                  f'{function_name}({arguments})'
        module, inferer = cs._parse_text(program)
        # get the Call node - there is only one in this test case.
        call_node = next(module.nodes_of_class(astroid.Call))
        function_call_type = call_node.type_constraints.type
        assert inferer.type_constraints.lookup_concrete(function_call_type) == call_node.args[i].type_constraints.type


if __name__ == '__main__':
    nose.main()
