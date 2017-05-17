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
    return "def " + function_name + "(" + ", ".join(args_list) + "):\n\t" + "return " + repr(return_value)


def _parse_text(source: str) -> astroid.Module:
    """Parse source code text and output an AST with type inference performed."""
    module = astroid.parse(source)
    environment_transformer().visit(module)
    register_type_constraints_setter().visit(module)
    return module


if __name__ == '__main__':
    nose.main()
