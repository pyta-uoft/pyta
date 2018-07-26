import astroid
import nose
from hypothesis import given, settings, HealthCheck
import tests.custom_hypothesis_support as cs
from tests.custom_hypothesis_support import lookup_type
import hypothesis.strategies as hs
from python_ta.typecheck.base import _node_to_type, TypeFailUnify, NoType
from typing import List, Set, Dict, Any, Tuple
from nose import SkipTest
from nose.tools import eq_
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


def test_annassign_subscript_list():
    program = """
    lst: List
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    assert issubclass(variable_type, List)


def test_annassign_subscript_list_int():
    program = """
    lst: List[int]
    
    lst = [1, 2, 3]
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    eq_(variable_type, List[int])

    assign_node = next(module.nodes_of_class(astroid.Assign))
    assign_type = lookup_type(inferer, assign_node, assign_node.targets[0].name)
    eq_(assign_type, List[int])


def test_annassign_subscript_list_int_wrong():
    program = """
    lst: List[int]

    lst = ['Hello', 'Goodbye']
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    eq_(variable_type, List[int])

    assign_node = next(module.nodes_of_class(astroid.Assign))
    assert isinstance(assign_node.inf_type, TypeFailUnify)


def test_annassign_subscript_set():
    program = """
    s: Set
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    assert issubclass(variable_type, Set)


def test_annassign_subscript_set_int():
    program = """
    s: Set[int]
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    eq_(variable_type, Set[int])


def test_annassign_subscript_dict():
    program = """
    d: Dict
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    assert issubclass(variable_type, Dict)


def test_annassign_subscript_dict_int_str():
    program = """
    d: Dict[int, str]
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    eq_(variable_type, Dict[int, str])


def test_annassign_subscript_tuple():
    program = """
    t: Tuple
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    assert issubclass(variable_type, Tuple)


def test_annassign_subscript_tuple_int():
    program = """
    t: Tuple[int, int]
    """
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    eq_(variable_type, Tuple[int, int])


def test_annassign_subscript_tuple_multi_param():
    program = """
    t: Tuple
    
    t = (1, 'Hello')
    """
    raise SkipTest("Requires support for multi-parameter Tuple annotations")
    module, inferer = cs._parse_text(program)
    ann_node = next(module.nodes_of_class(astroid.AnnAssign))
    variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
    eq_(variable_type, Tuple[int, int])


def test_annassign_subscript_multi_list():
    program = """
    l1: List
    l2: List
    
    l1 = [1, 2, 3]
    l2 = ['Hello', 'Goodbye']
    """
    module, inferer = cs._parse_text(program)

    for ann_node in module.nodes_of_class(astroid.AnnAssign):
        variable_type = lookup_type(inferer, ann_node, ann_node.target.name)
        assert issubclass(variable_type, List)

    assign_nodes = list(module.nodes_of_class(astroid.Assign))

    assign_node_1 = assign_nodes[0]
    assign_type_1 = lookup_type(inferer, assign_node_1, assign_node_1.targets[0].name)
    eq_(assign_type_1, List[Any])

    assign_node_2 = assign_nodes[1]
    assign_type_2 = lookup_type(inferer, assign_node_2, assign_node_2.targets[0].name)
    eq_(assign_type_2, List[Any])


def test_annassign_and_assign():
    src = """
    x: List[int] = [1, 2, 3]
    """
    module, inferer = cs._parse_text(src, reset=True)
    x = [inferer.lookup_typevar(node, node.name) for node
         in module.nodes_of_class(astroid.AssignName)][0]
    for ann_node in module.nodes_of_class(astroid.AnnAssign):
        assert ann_node.inf_type == NoType()
    assert inferer.type_constraints.resolve(x).getValue() == List[int]


def test_invalid_annassign_and_assign():
    src = """
    x: List[str] = [1, 2, 3]
    """
    module, inferer = cs._parse_text(src, reset=True)
    for ann_node in module.nodes_of_class(astroid.AnnAssign):
        assert isinstance(ann_node.inf_type, TypeFailUnify)


if __name__ == '__main__':
    nose.main()
