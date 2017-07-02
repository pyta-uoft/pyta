import astroid
import nose
from hypothesis import settings, given
from typing import List
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.homogeneous_iterable)
def test_list_comprehension_single_target_name_homogeneous_iterable(iterable):
    """Test Comprehension node visitor representing a comprehension expression with a single target and a
    name expression over a homogeneous list."""
    program = f'[num for num in {repr(iterable)}]'
    module, typeinferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    expected_type = List[listcomp_node.generators[0].iter.type_constraints.type.__args__[0]]
    assert listcomp_node.type_constraints.type == expected_type


@given(cs.homogeneous_iterable)
def test_list_comprehension_single_target_name_heterogeneous_iterable(iterable):
    """Test Comprehension node visitor representing a comprehension expression with a single target and a
    name expression over a heterogeneous list."""
    program = f'[num for num in {repr(iterable)}]'
    module, typeinferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    expected_type = List[listcomp_node.generators[0].iter.type_constraints.type.__args__[0]]
    assert listcomp_node.type_constraints.type == expected_type


@given(cs.valid_identifier(min_size=1))
def test_list_comprehension_single_target_name_string(iterable):
    """Test Comprehension node visitor representing a comprehension expression with a single target and a
    name expression over a string."""
    program = f'[num for num in {repr(iterable)}]'
    module, typeinferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    expected_type = List[listcomp_node.generators[0].iter.type_constraints.type]
    assert listcomp_node.type_constraints.type == expected_type


if __name__ == '__main__':
    nose.main()
