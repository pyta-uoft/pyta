from typing import *
from python_ta.typecheck.base import _TNode, TypeResult, TypeInfo, TypeFail, TypeConstraints
from nose import SkipTest
from nose.tools import eq_, assert_is_not_none
from astroid import extract_node
from tests.custom_hypothesis_support import _parse_text


def _create_TNode(type, parent=None, ast_node=None, ctx_node=None, origin=None):
    return _TNode(type, parent, ast_node, ctx_node, origin) # implementation specific


def _node_eq(node1, node2):
    if node1 is None or node2 is None:
        eq_(node1, node2)
    eq_(node1.type, node2.type)
    _node_eq(node1.parent, node2.parent)
    eq_(node1.ast_node.as_string(), node2.ast_node.as_string())
    eq_(node1.ctx_node.as_string(), node2.ctx_node.as_string())


def _nodes_to_dict(node_list):
    node_dict = {}
    for node in node_list:
        node_list[node.type] = node
    return node_dict


def _find_type_fail(ast_node):
    if isinstance(ast_node.inf_type, TypeFail):
        return ast_node
    else:
        for child in ast_node.get_children():
            child_res = _find_type_fail(child)
            if child_res is not None:
                return child_res
    return None


def _verify_inference(program, node_list):
    """Verify that type inference on 'program' produces same disjoint-set
       structure as the one represented by the nodes in 'node_list'."""
    _, inferer = _parse_text(program)
    actual_node_dict = _nodes_to_dict(node_list)
    expected_node_dict = _nodes_to_dict(inferer.type_constraints._nodes)
    eq_(sorted(actual_node_dict.keys()), sorted(expected_node_dict.keys()))
    for type in actual_node_dict.keys():
        _node_eq(actual_node_dict[type], expected_node_dict[type])


def _verify_type_fail(program, exp_node_str):
    fail_node = _find_type_fail(program)
    assert_is_not_none(fail_node, "Typecheck did not fail!")
    eq_(fail_node.as_string(), exp_node_str)
    eq_(fail_node.inf_type.src_node.as_string(), exp_node_str)


def test_ex1():
    raise SkipTest()
    program = \
        """
        x = 3
        x = 'abc'
        """
    int_node = _create_TNode(int, None, extract_node('3'))
    str_node = _create_TNode(str, None, extract_node('abc'))
    t0_node = _create_TNode(TypeVar("~T0"), int_node, extract_node('x'),
                            extract_node('x=3'))
    _verify_inference(program, [int_node, str_node, t0_node])
    _verify_type_fail(program, "x = 'abc'")
