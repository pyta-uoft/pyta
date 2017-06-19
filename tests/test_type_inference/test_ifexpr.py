import astroid
import nose
from hypothesis import given, settings, assume
from typing import Any
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.eval_types.flatmap(lambda s: hs.lists(s(), min_size=2, max_size=2)))
def test_ifexp_homogeneous(suites):
    """Test the type setting of an IfExp node representing an if statement."""
    program = f'a = {repr(suites[0])}  if True else {repr(suites[1])}\n'
    module, TypeInferrer = cs._parse_text(program)
    ifexp_node = list(module.nodes_of_class(astroid.IfExp))[0]
    assert ifexp_node.type_constraints.type == ifexp_node.body.type_constraints.type


@given(hs.lists(cs.eval_values, min_size=2, max_size=2))
def test_ifexp_heterogeneous(suites):
    """Test the type setting of an IfExp node representing an if statement."""
    assume(type(suites[0]) != type(suites[1]))
    program = f'a = {repr(suites[0])}  if True else {repr(suites[1])}\n'
    module, TypeInferrer = cs._parse_text(program)
    ifexp_node = list(module.nodes_of_class(astroid.IfExp))[0]
    assert ifexp_node.type_constraints.type == Any


if __name__ == '__main__':
    nose.main()
