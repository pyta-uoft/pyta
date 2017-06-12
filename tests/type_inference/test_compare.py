import astroid
import nose
from hypothesis import given, settings, assume
from typing import GenericMeta
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.primitive_values, hs.lists(hs.tuples(cs.comparator_operator, cs.primitive_values), min_size=1))
def test_compare_builtins(left_value, operator_value_tuples):
    """Test type settting of Compare node representing comparison between primitive values."""
    for operator, value in operator_value_tuples:
        if operator == 'in' or operator == 'is':
            assume(isinstance(value, GenericMeta))
    program = f'{repr(left_value)} '
    for operator, value in operator_value_tuples:
        program += ' '.join([operator, repr(value)])
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.type_constraints.type == bool


if __name__ == '__main__':
    nose.main()
