import astroid
import nose
from hypothesis import given, settings
from typing import Callable
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


def test_for_list():
    """Test whether visitors properly set the type constraint of the a For node representing for/else statement
     iterating over a simple list.
    """
    program = f'for num in [1, 2, 3]:\n' \
              f'    x = 3 + num\n' \
              f'else:\n' \
              f'    pass\n'
    module, TypeInferrer = cs._parse_text(program)
    for_node = list(module.nodes_of_class(astroid.For))[0]
    local_type_var = module.type_environment.lookup_in_env('x')
    inferred_type = TypeInferrer.type_constraints.lookup_concrete(local_type_var)
    assert inferred_type == int


def test_inference_func_def_for():
    """Test whether visitors properly set the type constraint of the a For node representing for/else statement
     iterating over a more complex iterable (ie, tuples, dicts, nested iterables).
    """
    program = f'x = 5\n' \
              f'\n' \
              f'def add_ten(x):\n' \
              f'    for num in [1, 2, 3, 4]:\n' \
              f'        x = x + num\n' \
              f'    return x\n' \
              f'\n' \
              f'add_ten(5)\n' \
              f''
    module, TypeInferrer = cs._parse_text(program)
    for_node = list(module.nodes_of_class(astroid.For))[0]
    function_def_node = list(module.nodes_of_class(astroid.FunctionDef))[0]
    function_type_var = module.type_environment.lookup_in_env(function_def_node.name)
    function_type = TypeInferrer.type_constraints.lookup_concrete(function_type_var)
    target_type_var = function_def_node.type_environment.lookup_in_env('num')
    target_type = TypeInferrer.type_constraints.lookup_concrete(target_type_var)
    assert (function_type == Callable[[int], int]) and (target_type == int)


if __name__ == '__main__':
    nose.main()
