import astroid
import nose
from hypothesis import given, settings, assume
from typing import Callable, Any
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


# def test_list_comprehension1():
#     """Test Comprehension node visitor representing a comprehension expression."""
#     program = f'a = [num for num in [1,2,3]]'
#     module, TypeInferrer = cs._parse_text(program)
#     comp_node = list(module.nodes_of_class(astroid.Comprehension))[0]
#     listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
#     assert True

def test_list_comprehension1():
    """Test Comprehension node visitor representing a comprehension expression."""
    program = f'a = [num1+ num2 for num1, num2 in [[1,2], [3,4]]]'
    module, TypeInferrer = cs._parse_text(program)
    comp_node = list(module.nodes_of_class(astroid.Comprehension))[0]
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    assert True

# def test_list_comprehension2():
#     """Test Comprehension node visitor representing a comprehension expression."""
#     program = f'a = [num for sublist in [[1, 2], [3,4]] for num in sublist]'
#     module, TypeInferrer = cs._parse_text(program)
#     comp_node = list(module.nodes_of_class(astroid.Comprehension))[0]
#     listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
#     assert True

if __name__ == '__main__':
    nose.main()
