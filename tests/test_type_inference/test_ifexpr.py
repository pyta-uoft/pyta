import astroid
import nose
from hypothesis import given, settings
from typing import Any
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


@given(cs.ifexp_node())
def test_ifexp(node):
    """Test the type setting of an IfExp node representing an if statement."""
    module, type_inferer = cs._parse_text(node)
    for ifexp_node in module.nodes_of_class(astroid.IfExp):
        if type_inferer.type_constraints.can_unify(
                        ifexp_node.body.type_constraints.type,
                        ifexp_node.orelse.type_constraints.type):
            assert ifexp_node.type_constraints.type == ifexp_node.body.type_constraints.type
        else:
            assert ifexp_node.type_constraints.type == Any


if __name__ == '__main__':
    nose.main()
