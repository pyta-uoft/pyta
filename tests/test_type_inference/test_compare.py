import astroid
import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.primitive_values, hs.lists(hs.tuples(cs.comparator_operator_equality, cs.primitive_values), min_size=1))
def test_compare_equality(left_value, operator_value_tuples):
    """Test type setting of Compare node representing comparators: ''==', '!=', '>=', '<=', 'is'. """
    for operator, value in operator_value_tuples:
        if isinstance(value, str):
            assume(len(value) > 2)
    program = f'{repr(left_value)} '
    for operator, value in operator_value_tuples:
        program += ' '.join([operator, repr(value)])
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.type_constraints.type == bool


@given(hs.lists(cs.comparator_operator, min_size=3), cs.homogeneous_list(min_size=4))
def test_compare_equality(operators, values):
    """Test type setting of Compare node representing comparators: '<', '>', 'in'. """
    for value in values:
        assume(value)
        if isinstance(value, str):
            assume(len(value) > 2)
    a = list(zip(operators, values))
    pre = []
    for operator, value in a:
        pre.append(str(operator))
        pre.append(str(value))
    # pre_input_program = [str(elt) for tuple in zip(operator, values) for elt in tuple]
    program = f'{str(values[0])} ' + ' '.join(pre)
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.type_constraints.type == bool


if __name__ == '__main__':
    nose.main()
