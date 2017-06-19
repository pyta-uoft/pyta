import astroid
import nose
from hypothesis import given, settings, assume
from typing import Callable, Any
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


def test_ifexp_homogeneous():
    """Test the type setting of an IfExp node representing an if statement."""
    program = f'a = 2 + 1 if True else 0\n'
    module, TypeInferrer = cs._parse_text(program)
    ifexp_node = list(module.nodes_of_class(astroid.IfExp))[0]
    assert ifexp_node.type_constraints.type == ifexp_node.body.type_constraints.type


def test_ifexp_heterogeneous():
    """Test the type setting of an IfExp node representing an if statement."""
    program = f'a = \"bob\" if True else 0\n'
    module, TypeInferrer = cs._parse_text(program)
    ifexp_node = list(module.nodes_of_class(astroid.IfExp))[0]
    assert ifexp_node.type_constraints.type == Any


if __name__ == '__main__':
    nose.main()
