import astroid

from python_ta.typecheck.base import TypeFail
from hypothesis import given, settings, assume, HealthCheck
from .. import custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(hs.integers(), hs.lists(hs.tuples(cs.comparator_operator_equality, hs.integers()), min_size=1))
@settings(deadline=None)
def test_compare_equality(left_value, operator_value_tuples):
    """Test type setting of Compare node representing comparators: ''==', '!=', '>=', '<=', 'is'. """
    program = f'{repr(left_value)}'
    for operator, value in operator_value_tuples:
        program += ' ' + ' '.join([operator, repr(value)])
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.inf_type.getValue() == bool


@given(hs.lists(cs.comparator_operator, min_size=3), cs.numeric_list(min_size=4))
@settings(deadline=None)
def test_compare_inequality(operators, values):
    """Test type setting of Compare node representing comparators: '<', '>'. """
    a = list(zip(operators, values))
    pre = []
    for operator, value in a:
        pre.append(str(operator))
        pre.append(str(value))
    # pre_input_program = [str(elt) for tuple in zip(operator, values) for elt in tuple]
    program = f'{str(values[0])} ' + ' '.join(pre)
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.inf_type.getValue() == bool


def test_compare_in():
    """Test type setting of Compare node representing 'in' operator"""
    program = '0 in [1,2,3]'
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.inf_type.getValue() == bool


def test_compare_in_error():
    """Test type setting of Compare node representing invaliud use of 'in' operator"""
    program = '0 in 5'
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert isinstance(compare_node.inf_type, TypeFail)


def test_compare_is():
    program = """
    A = 0
    A is 1
    """
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.inf_type.getValue() == bool


def test_compare_is_not():
    program = """
    A = 0
    A is not 1
    """
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.inf_type.getValue() == bool


def test_compare_not_in():
    program = """
    A = [0, 1, 2]
    3 not in A
    
    """
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.inf_type.getValue() == bool


def test_compare_not_in_fail():
    program = """
    A = 5
    3 not in A

    """
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert isinstance(compare_node.inf_type, TypeFail)
