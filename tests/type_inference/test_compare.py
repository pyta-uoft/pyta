import astroid
import nose
from hypothesis import given, settings, assume
from typing import GenericMeta
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.primitive_values, hs.lists(hs.tuples(cs.comparator_operator, cs.primitive_values), min_size=1))
def test_compare_builtins(left_value, operator_value_tuples):
    """Test type setting of Compare node representing comparison between primitive values."""
    assume(left_value is not None)
    for operator, value in operator_value_tuples:
        assume(value is not None)
    if isinstance(left_value, int):
        for operator, value in operator_value_tuples:
            assume(not isinstance(value, float) and not isinstance(value, str) and not isinstance(value, bytes))
    if isinstance(left_value, float):
        for operator, value in operator_value_tuples:
            assume(not isinstance(value, int) and not isinstance(value, str) and not isinstance(value, bytes))
    if isinstance(left_value, str):
        for operator, value in operator_value_tuples:
            assume(not isinstance(value, int) and not isinstance(value, float) and not isinstance(value, bytes))
    if isinstance(left_value, bytes):
        for operator, value in operator_value_tuples:
            assume(not isinstance(value, str) and not isinstance(value, bool) and not isinstance(value, float) and not isinstance(value, int))
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
