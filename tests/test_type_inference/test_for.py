import astroid
import nose
from hypothesis import given, settings, assume
from typing import Callable, Any
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.homogeneous_list(min_size=1))
def test_for_homogeneous_list(iterable):
    """Test whether visitors properly set the type constraint of the a For node representing for/else statement
     iterating over a homogeneous list.
    """
    program = f'for elt in {iterable}:\n' \
              f'    x = elt\n'
    module, TypeInferrer = cs._parse_text(program)
    for_node = list(module.nodes_of_class(astroid.For))[0]
    local_type_var = module.type_environment.lookup_in_env('x')
    inferred_type = TypeInferrer.type_constraints.lookup_concrete(local_type_var)
    assert inferred_type == for_node.iter.type_constraints.type.__args__[0]


@given(cs.random_list(min_size=2))
def test_for_heterogeneous_list(iterable):
    """Test whether visitors properly set the type constraint of the a For node representing for/else statement
     iterating over a heterogeneous list.
    """
    assume(type(iterable[0]) != type(iterable[1]))
    val_types = [type(val) for val in iterable]
    if int in val_types:
        assume(bool not in val_types)
    if bool in val_types:
        assume(int not in val_types)
    program = f'for elt in {iterable}:\n' \
              f'    x = elt\n'
    module, TypeInferrer = cs._parse_text(program)
    for_node = list(module.nodes_of_class(astroid.For))[0]
    local_type_var = module.type_environment.lookup_in_env('x')
    inferred_type = TypeInferrer.type_constraints.lookup_concrete(local_type_var)
    assert inferred_type == Any


def test_inference_func_def_for():
    """Test whether visitors properly set the type constraint of the a For node representing for/else statement
     iterating over a more complex iterable (ie, tuples, dicts, nested iterables).
    """
    program = f'def add_ten(x):\n' \
              f'    for num in [1, 2, 3, 4]:\n' \
              f'        x = x + num\n' \
              f'    return x\n'
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
