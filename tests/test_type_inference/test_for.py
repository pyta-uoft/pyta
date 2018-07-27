import astroid
import nose
from hypothesis import given, settings, assume,  HealthCheck
from typing import Callable, Any, Tuple
import tests.custom_hypothesis_support as cs
from tests.custom_hypothesis_support import lookup_type
from nose.tools import eq_
from nose import SkipTest
settings.load_profile("pyta")


@given(cs.homogeneous_list(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_for_homogeneous_list(iterable):
    """Test whether visitors properly set the type constraint of the a For node representing for/else statement
     iterating over a homogeneous list.
    """
    program = f'for elt in {iterable}:\n' \
              f'    x = elt\n'
    module, TypeInferrer = cs._parse_text(program)
    for_node = list(module.nodes_of_class(astroid.For))[0]
    local_type_var = module.type_environment.lookup_in_env('x')
    inferred_type = TypeInferrer.type_constraints.resolve(local_type_var).getValue()
    assert inferred_type == for_node.iter.inf_type.getValue().__args__[0]


@given(cs.random_list(min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow])
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
    inferred_type = TypeInferrer.type_constraints.resolve(local_type_var).getValue()
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
    function_type = TypeInferrer.type_constraints.resolve(function_type_var).getValue()
    target_type_var = function_def_node.type_environment.lookup_in_env('num')
    target_type = TypeInferrer.type_constraints.resolve(target_type_var).getValue()
    assert (function_type == Callable[[int], int]) and (target_type == int)


def test_for_dict():
    program = """
        some_dict = {'A': 1, 'B': 2}

        for a, b in some_dict:
            x = a
            y = b
        """
    module, ti = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.AssignName):
        if assign_node.name == 'x' or assign_node.name == 'a':
            eq_(lookup_type(ti, assign_node, assign_node.name), str)
        elif assign_node.name == 'y' or assign_node.name == 'b':
            eq_(lookup_type(ti, assign_node, assign_node.name), int)


def test_for_list_tuple():
    program = """
        some_list = [('A', 1), ('B', 2)]

        for elt in some_list:
            x = elt
        """
    module, ti = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.AssignName):
        if assign_node.name == 'x' or assign_node.name == 'elt':
            eq_(lookup_type(ti, assign_node, assign_node.name), Tuple[str, int])


def test_for_list_tuple_multi_arg():
    program = """
        some_list = [('A', 1), ('B', 2)]

        for a, b in some_list:
            x = a
            y = b
        """
    module, ti = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.AssignName):
        if assign_node.name == 'x' or assign_node.name == 'a':
            eq_(lookup_type(ti, assign_node, assign_node.name), str)
        elif assign_node.name == 'y' or assign_node.name == 'b':
            eq_(lookup_type(ti, assign_node, assign_node.name), int)


def test_for_zip():
    program = """
        some_str_list = ['A', 'B']
        some_int_list = [1, 2]

        for a, b in zip(some_str_list, some_int_list):
            x = a
            y = b
        """
    module, ti = cs._parse_text(program)
    raise SkipTest(f'Type signature of zip inferred incorrectly due to lookup_typevar '
                   f'using the first available function in type_store.functions[zip]')
    for assign_node in module.nodes_of_class(astroid.AssignName):
        if assign_node.name == 'x' or assign_node.name == 'a':
            eq_(lookup_type(ti, assign_node, assign_node.name), str)
        elif assign_node.name == 'y' or assign_node.name == 'b':
            eq_(lookup_type(ti, assign_node, assign_node.name), int)


if __name__ == '__main__':
    nose.main()
