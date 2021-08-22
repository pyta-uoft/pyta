from typing import Set, _GenericAlias

from astroid import nodes
from hypothesis import HealthCheck, given, settings

from .. import custom_hypothesis_support as cs

settings.load_profile("pyta")


@given(cs.homogeneous_iterable)
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_comprehension_reproduce_homogeneous(iterable):
    """Test SetComp node visitor representing a comprehension expression reproducing a set of elements of
    a homogeneous iterable."""
    program = "{elt for elt in " + repr(iterable) + "}"
    module, _ = cs._parse_text(program)
    setcomp_node = list(module.nodes_of_class(nodes.SetComp))[0]
    assert (
        setcomp_node.inf_type.getValue()
        == Set[setcomp_node.generators[0].iter.inf_type.getValue().__args__[0]]
    )


@given(cs.heterogeneous_iterable)
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_comprehension_reproduce_heterogeneous(iterable):
    """Test SetComp node visitor representing a comprehension expression reproducing a set of elements of
    a heterogeneous iterable."""
    program = "{elt for elt in " + repr(iterable) + "}"
    module, _ = cs._parse_text(program)
    setcomp_node = list(module.nodes_of_class(nodes.SetComp))[0]
    assert (
        setcomp_node.inf_type.getValue()
        == Set[setcomp_node.generators[0].iter.inf_type.getValue().__args__[0]]
    )


@given(cs.valid_identifier(min_size=1))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_set_comprehension_reproduce_string(iterable):
    """Test SetComp node visitor representing a comprehension expression reproducing a set of elements of
    a string."""
    program = "{elt for elt in " + repr(iterable) + "}"
    module, _ = cs._parse_text(program)
    setcomp_node = list(module.nodes_of_class(nodes.SetComp))[0]
    assert (
        setcomp_node.inf_type.getValue() == Set[setcomp_node.generators[0].iter.inf_type.getValue()]
    )
