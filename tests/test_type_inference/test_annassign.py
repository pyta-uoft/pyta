import astroid
import nose
from hypothesis import given, assume, settings, HealthCheck
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from typing import TypeVar, Any
from python_ta.typecheck.base import _node_to_type
settings.load_profile("pyta")


@given(hs.dictionaries(cs.valid_identifier(), cs.annotation, min_size=2))
def test_annassign_concrete(variables_annotations_dict):
    """Test whether types are being properly set for an AnnAssign node.
    """
    program = f'class Student:\n' \
              f'    name: str\n' \
              f'    age: int\n' \
              f'    status: bool\n' \
              f'    def __init__(self):\n' \
              f'        pass\n' \
              f''
    module, inferer = cs._parse_text(program)
    for node in module.nodes_of_class(astroid.AnnAssign):
        # variable_type = self._find_type(node, node.target.name)
        variable_type = inferer.type_constraints.lookup_concrete(
            inferer._closest_frame(node, node.target.name).type_environment.lookup_in_env(node.target.name))
        # TODO: we don't want to evaluate.. Just hard code and test builtins?
        annotated_type = _node_to_type(node.annotation.name)
        assert variable_type == annotated_type


if __name__ == '__main__':
    nose.main()
