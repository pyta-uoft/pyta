import astroid
import nose
from hypothesis import assume, given
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Callable
from python_ta.transforms.type_inference_visitor import TYPE_CONSTRAINTS
from keyword import iskeyword


def _parse_to_function(function_name, args_list, return_statement):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):' \
           f'   return {repr(return_statement)}'


def _parse_to_function_no_return(function_name, args_list, return_statement):
    """Helper to parse given data into function definition."""
    return f'def {function_name}({", ".join(args_list)}):\n' \
           f'     {return_statement}'


@given(cs.valid_identifier(), cs.primitive_values)
def test_function_def_no_args(function_name, return_statement):
    """Test FunctionDef node visitors representing function definitions with no parameters and primitive return type."""
    assume(not iskeyword(function_name))
    program = _parse_to_function(function_name, [], return_statement)
    module = cs._parse_text(program)
    function_type_var = module.type_environment.lookup_in_env(function_name)
    assert TYPE_CONSTRAINTS.lookup_concrete(function_type_var) == Callable[[], type(return_statement)]


@given(cs.valid_identifier(), cs.primitive_values)
def test_function_def_call_no_args(function_name, return_value):
    """Test type setting in environment of a function call for a function with no parameters."""
    TYPE_CONSTRAINTS.clear_tvars()
    program = _parse_to_function(function_name, [], return_value) + "\n" + function_name + "()\n"
    module = cs._parse_text(program)
    # there should be a single Expr node in this program
    expr_node = next(module.nodes_of_class(astroid.Expr))
    assert expr_node.type_constraints.type == type(return_value)


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=0), cs.primitive_values)
def test_function_def_no_return(function_name, arguments, body):
    """Test FunctionDef node visitors representing non-returning function definitions with parameter(s)."""
    for return_value in ['return None', repr(body), 'pass']:
        program = _parse_to_function_no_return(function_name, arguments, return_value)
        module = cs._parse_text(program)
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [TYPE_CONSTRAINTS.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        assert TYPE_CONSTRAINTS.lookup_concrete(function_type_var) == Callable[expected_arg_types, None]


if __name__ == '__main__':
    nose.main()
