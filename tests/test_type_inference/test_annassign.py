import astroid
import nose
from hypothesis import given, settings, HealthCheck
import tests.custom_hypothesis_support as cs
from tests.custom_hypothesis_support import lookup_type
import hypothesis.strategies as hs
from python_ta.typecheck.base import _node_to_type
settings.load_profile("pyta")


def test_annassign_concrete():
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
        variable_type = lookup_type(inferer, node, node.target.name)
        annotated_type = _node_to_type(node.annotation.name)
        assert variable_type == annotated_type


@given(hs.dictionaries(cs.valid_identifier(), cs.builtin_type, min_size=2))
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_annassign(variables_annotations_dict):
    """Test whether types are being properly set for an AnnAssign node.
    """
    program = f'class Student:\n'
    for variable in variables_annotations_dict:
        program += f'    {variable}: {variables_annotations_dict[variable].__name__}\n'
    program += f'    def __init__(self):\n' \
               f'        pass\n'
    module, inferer = cs._parse_text(program)
    for node in module.nodes_of_class(astroid.AnnAssign):
        variable_type = lookup_type(inferer, node, node.target.name)
        annotated_type = variables_annotations_dict[node.target.name]
        assert variable_type == annotated_type


if __name__ == '__main__':
    nose.main()
