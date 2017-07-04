import astroid
import nose
from hypothesis import settings, given
import tests.custom_hypothesis_support as cs
from typing import Set, GenericMeta
settings.load_profile("pyta")


@given(cs.homogeneous_iterable)
def test_set_comprehension_reproduce_homogeneous(iterable):
    """Test SetComp node visitor representing a comprehension expression reproducing a set of elements of
    a homogeneous iterable."""
    program = '{elt for elt in ' + repr(iterable) + '}'
    module, _ = cs._parse_text(program)
    setcomp_node = list(module.nodes_of_class(astroid.SetComp))[0]
    assert setcomp_node.type_constraints.type == Set[setcomp_node.generators[0].iter.type_constraints.type.__args__[0]]


@given(cs.heterogeneous_iterable)
def test_set_comprehension_reproduce_heterogeneous(iterable):
    """Test SetComp node visitor representing a comprehension expression reproducing a set of elements of
    a heterogeneous iterable."""
    program = '{elt for elt in ' + repr(iterable) + '}'
    module, _ = cs._parse_text(program)
    setcomp_node = list(module.nodes_of_class(astroid.SetComp))[0]
    assert setcomp_node.type_constraints.type == Set[setcomp_node.generators[0].iter.type_constraints.type.__args__[0]]


@given(cs.valid_identifier(min_size=1))
def test_set_comprehension_reproduce_string(iterable):
    """Test SetComp node visitor representing a comprehension expression reproducing a set of elements of
    a string."""
    program = '{elt for elt in ' + repr(iterable) + '}'
    module, _ = cs._parse_text(program)
    setcomp_node = list(module.nodes_of_class(astroid.SetComp))[0]
    assert setcomp_node.type_constraints.type == Set[setcomp_node.generators[0].iter.type_constraints.type]

if __name__ == '__main__':
    nose.main()
