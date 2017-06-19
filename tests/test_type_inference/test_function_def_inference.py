import astroid
import nose
from hypothesis import assume, given, settings
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Callable
settings.load_profile("pyta")


def _parse_to_function(function_name, args_list, return_statement):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):' \
           f'    return {return_statement}'


def _parse_to_function_no_return(function_name, args_list, function_body):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):\n' \
           f'    {function_body}'


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=1))
def test_inference_args_simple_return(function_name, arguments):
    """Test whether visitor was able to infer type of argument given function called on it in function body."""
    assume(function_name not in arguments)
    for argument in arguments:
        program = _parse_to_function_no_return(function_name, arguments, ('return ' + argument + " + " + repr('bob')))
        module, inferer = cs._parse_text(program)
        # get the functionDef node - there is only one in this test case.
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = inferer.type_constraints.lookup_concrete(function_type_var)
        actual_arg_types, actual_return_type = inferer.type_constraints.types_in_callable(function_type)
        assert expected_arg_types == actual_arg_types


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=1))
def test_function_def_args_simple_return(function_name, arguments):
    """Test whether visitor was able to infer type of function given function called on it's arguments."""
    assume(function_name not in arguments)
    for argument in arguments:
        program = _parse_to_function_no_return(function_name, arguments, ('return ' + argument + " + " + repr('bob')))
        module, inferer = cs._parse_text(program)
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = inferer.type_constraints.lookup_concrete(function_type_var)
        actual_arg_types, actual_return_type = inferer.type_constraints.types_in_callable(function_type)
        return_type_var = function_def_node.type_environment.lookup_in_env(argument)
        expected_return_type = inferer.type_constraints.lookup_concrete(return_type_var)
        assert Callable[actual_arg_types, actual_return_type] == Callable[expected_arg_types, expected_return_type]


if __name__ == '__main__':
    nose.main()
