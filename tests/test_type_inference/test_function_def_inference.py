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


def _parse_to_annotated_function(function_name, args_list, return_statement, annotations):
    """Helper to parse given data into function definition."""
    args_annotations = zip(args_list, annotations[:-1])
    pre_process = [f'{arg}: {annotation}' for arg, annotation in args_annotations]
    return f'def {function_name}({", ".join(pre_process)}) -> {annotations[-1]}:' \
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


@given(cs.valid_identifier(), hs.lists(cs.valid_identifier(), min_size=2), hs.lists(cs.annotation, min_size=3))
def test_functiondef_annotated_simple_return(function_name, arguments, annotations):
    """Test whether type annotations are set properly for a FunctionDef node representing a function definition
    with type annotations."""
    # TODO: 2 test cases?... one for args, one for return?
    assume(function_name not in arguments and len(arguments) == len(annotations) - 1)
    [assume(annotation is not None) for annotation in annotations]
    program = _parse_to_annotated_function(function_name
                                           , arguments, (arguments[0]), annotations)
    module, inferer = cs._parse_text(program)
    functiondef_node = next(module.nodes_of_class(astroid.FunctionDef))
    # arguments and annotations are not changing, so test this once.
    for i in range(len(functiondef_node.args.annotations)):
        arg_name = functiondef_node.args.args[i].name
        actual_type = inferer.type_constraints.lookup_concrete(functiondef_node.type_environment.lookup_in_env(arg_name))
        assert actual_type.__name__ == functiondef_node.args.annotations[i].name
    # test return type annotations
    for i in range(len(arguments)):
        annotations[-1] = annotations[i]
        program = _parse_to_annotated_function(function_name
                                               , arguments, (arguments[i]), annotations)
        module, inferer = cs._parse_text(program)
        functiondef_node = next(module.nodes_of_class(astroid.FunctionDef))
        expected_arg_type_vars = [functiondef_node.type_environment.lookup_in_env(argument) for argument in arguments]
        expected_arg_types = [inferer.type_constraints.lookup_concrete(type_var) for type_var in expected_arg_type_vars]
        function_type_var = module.type_environment.lookup_in_env(function_name)
        function_type = inferer.type_constraints.lookup_concrete(function_type_var)
        actual_arg_types, actual_return_type = inferer.type_constraints.types_in_callable(function_type)
        assert expected_arg_types == actual_arg_types and functiondef_node.returns.name == actual_return_type.__name__


if __name__ == '__main__':
    nose.main()
