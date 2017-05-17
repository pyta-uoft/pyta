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
    return f'def {function_name}({", ".join(args_list)}):' \
           f'   return {repr(return_value)}'


@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1), cs.primitive_values)
def test_function_def_no_args(function_name, return_value):
    """Test FunctionDef node visitors representing function definitions with no parameters and primitive return val."""
    assume(not iskeyword(function_name))
    program = _parse_to_function(function_name, [], return_value)
    module = cs._parse_text(program)
    function_type_var = module.type_environment.lookup_in_env(function_name)
    assert TYPE_CONSTRAINTS.lookup_concrete(function_type_var) == Callable[[], type(return_value)]


@given(hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1), cs.primitive_values)
def test_function_def_call_no_args(function_name, return_value):
    """Test type setting in environment of a function call for a function with no parameters."""
    TYPE_CONSTRAINTS.clear_tvars()
    assume(not iskeyword(function_name))
    program = _parse_to_function(function_name, [], return_value) + "\n" + function_name + "()\n"
    module = cs._parse_text(program)
    # there should be a single call node in this program
    call_node = next(module.nodes_of_class(astroid.Call))
    assert call_node.type_constraints.type == type(return_value)


if __name__ == '__main__':
    nose.main()
