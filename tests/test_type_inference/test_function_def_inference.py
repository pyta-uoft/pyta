import astroid
import nose
from hypothesis import assume, given, settings, HealthCheck
from unittest import SkipTest
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import Callable, _ForwardRef, Type
from nose.tools import eq_
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
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_inference_args_simple_return(function_name, arguments):
    """Test whether visitor was able to infer type of argument given function called on it in function body."""
    assume(function_name not in arguments)
    for argument in arguments:
        program = _parse_to_function_no_return(function_name, arguments, ('return ' + argument + " + " + repr('bob')))
        module, inferer = cs._parse_text(program)
        # get the functionDef node - there is only one in this test case.
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.resolve(type_var).getValue() for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = inferer.type_constraints.resolve(function_type_var).getValue()
        actual_arg_types, actual_return_type = inferer.type_constraints.types_in_callable(function_type)
        assert expected_arg_types == actual_arg_types


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_function_def_args_simple_return(function_name, arguments):
    """Test whether visitor was able to infer type of function given function called on its arguments."""
    assume(function_name not in arguments)
    for argument in arguments:
        program = _parse_to_function_no_return(function_name, arguments, ('return ' + argument + " + " + repr('bob')))
        module, inferer = cs._parse_text(program)
        function_def_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [function_def_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.resolve(type_var).getValue() for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = inferer.type_constraints.resolve(function_type_var).getValue()
        actual_arg_types, actual_return_type = inferer.type_constraints.types_in_callable(function_type)
        return_type_var = function_def_node.type_environment.lookup_in_env(argument)
        expected_return_type = inferer.type_constraints.resolve(return_type_var).getValue()
        assert Callable[actual_arg_types, actual_return_type] == Callable[expected_arg_types, expected_return_type]


@given(cs.functiondef_node(annotated=True, returns=True))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_functiondef_annotated_simple_return(functiondef_node):
    """Test whether type annotations are set properly for a FunctionDef node representing a function definition
    with type annotations."""
    arg_names = [arg.name for arg in functiondef_node.args.args]
    assume(functiondef_node.name not in arg_names)
    for arg in functiondef_node.args.args:
        assume(arg_names.count(arg.name) == 1)
    module, inferer = cs._parse_text(functiondef_node)
    functiondef_node = next(module.nodes_of_class(astroid.FunctionDef))
    # arguments and annotations are not changing, so test this once.
    for i in range(len(functiondef_node.args.annotations)):
        arg_name = functiondef_node.args.args[i].name
        expected_type = inferer.type_constraints.resolve(functiondef_node.type_environment.lookup_in_env(arg_name)).getValue()
        # need to do by name because annotations must be name nodes.
        assert expected_type.__name__ == functiondef_node.args.annotations[i].name
    # test return type
    return_node = functiondef_node.body[0].value
    expected_rtype = inferer.type_constraints.resolve(functiondef_node.type_environment.lookup_in_env(return_node.name)).getValue()
    assert expected_rtype.__name__ == functiondef_node.returns.name


def test_functiondef_method():
    program = \
        '''
        class A:

            def method(self, x):
                return x + 1
        '''
    module, inferer = cs._parse_text(program)
    for func_def in module.nodes_of_class(astroid.FunctionDef):
        assert inferer.lookup_type(func_def, func_def.argnames()[0]) == _ForwardRef('A')


def test_functiondef_classmethod():
    program = \
        '''
        class A:

            @classmethod
            def method(cls, x):
                return x + 1
        '''
    module, inferer = cs._parse_text(program)
    for func_def in module.nodes_of_class(astroid.FunctionDef):
        assert inferer.lookup_type(func_def, func_def.argnames()[0]) == Type[_ForwardRef('A')]


def test_functiondef_staticmethod():
    program = \
        '''
        class A:

            @staticmethod
            def method(x):
                return x + 1
        '''
    module, inferer = cs._parse_text(program)
    for func_def in module.nodes_of_class(astroid.FunctionDef):
        assert inferer.lookup_type(func_def, func_def.argnames()[0]) == int



def test_nested_annotated_function_conflicting_body():
    """ User tries to define an annotated function which has conflicting types within its body.
    """
    program = f'def random_func(int1: int) -> None:\n' \
              f'    int1 + "bob"\n'

    raise SkipTest("Outdated annotation test. Previously raised SkipTest during cs._parse_text")

    try:
        module, inferer = cs._parse_text(program)
    except:
        raise SkipTest()
    functiondef_type = inferer.lookup_type(module, "return_int")
    expected_msg = f'In the FunctionDef node in line 1, in the annotated Function Definition of "random_func" in line 1:\n' \
                   f'in parameter (1), "int1", the annotated type is int, which conflicts with the inferred type of ' \
                   f'str from the function definition body.'
                    # TODO: where in the body, or is this too convoluted? Extract from sets.
    assert functiondef_type.msg == expected_msg


def test_annotated_functiondef_conflicting_return_type():
    """ User defines an annotated function with type errors in it's body;
    a discrepancy in annotated return type versus return type in it's body.
    """
    program = f'def return_str(num1: int, str1: str) -> int:\n' \
              f'    output = num1 + str1\n' \
              f'    return "bob"\n' \
              f'\n'
    try:
        module, inferer = cs._parse_text(program)
    except:
        raise SkipTest()
    functiondef_type = inferer.lookup_type(module, "return_str")
    expected_msg = f'In the FunctionDef node in line 1, in the annotated Function Definition of "random_func" in line 1:\n' \
                   f'the annotated return type is int, which conflicts with the inferred return type of ' \
                   f'str from the function definition body.'
    assert functiondef_type.msg == expected_msg


def test_function_return():
    program = """
    def foo(x):
        return x
    
    foo(1)
    """
    module, inferer = cs._parse_text(program)
    call_node = next(module.nodes_of_class(astroid.Call))
    func_type = call_node.func.inf_type.getValue()
    t1, t2 = func_type.__args__
    eq_(t1, t2)


def test_function_return_2():
    program = """
    def foo(x, y):
        return x
    
    foo(1,2)
    """
    module, inferer = cs._parse_text(program)
    call_node = next(module.nodes_of_class(astroid.Call))
    func_type = call_node.func.inf_type.getValue()
    t1, t2, t3 = func_type.__args__
    eq_(t1, t3)


def test_function_return_3():
    program = """
    def foo(x, y):
        return y
    
    foo(1,2)
    """
    module, inferer = cs._parse_text(program)
    call_node = next(module.nodes_of_class(astroid.Call))
    func_type = call_node.func.inf_type.getValue()
    t1, t2, t3 = func_type.__args__
    eq_(t2, t3)


if __name__ == '__main__':
    nose.main()
