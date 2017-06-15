import astroid
import nose
from hypothesis import given, settings
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
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


# def test_inference_list_subscript(input_list, index):
#     """Test whether visitors properly set the type constraint of the a For node representing for/else statement
#      iterating over a more complex iterable (ie, tuples, dicts, nested iterables).
#     """
#     program = f'num1 = \'bob\'\n' \
#               f'for num1, num2 in [(1, 2), (3, 3)]:\n' \
#               f'    x = 3 + num2\n' \
#               f'else:\n' \
#               f'    pass\n' \
#               f'x'
#     module, TypeInferrer = cs._parse_text(program)
#     for_node = list(module.nodes_of_class(astroid.For))[0]


if __name__ == '__main__':
    nose.main()
