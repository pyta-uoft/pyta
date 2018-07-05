import astroid
import tests.custom_hypothesis_support as cs
from python_ta.typecheck.base import TypeFail, TypeFailUnify
from tests.test_type_inference.test_tnode_structure import find_type_fail
from nose.tools import eq_


def verify_typefail_unify(tf: TypeFailUnify, *exp_tnodes, exp_src_type, num_reasons):
    assert isinstance(tf, TypeFailUnify)
    for tn, exp_r in zip(tf.tnodes, exp_tnodes):
        if tn.ast_node:
            eq_(tn.ast_node.name, exp_r)
        else:
            eq_(tn.type, exp_r)
    assert isinstance(tf.src_node, exp_src_type)

    reasons = []
    for tn in tf.tnodes:
        reasons += tn.find_path_to_parent()
    eq_(len(reasons), num_reasons)


def test_var_assign():
    src = """
    A = 1
    A = 'One'
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'A', str, exp_src_type=astroid.Assign, num_reasons=1)


def test_two_var_assign():
    src = """
    A = 1
    B = 'Two'
    A = B
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'A', 'B', exp_src_type=astroid.Assign, num_reasons=2)


def test_var_chain():
    src = """
    A = 1
    Z = 'Zed'

    B = A
    C = B
    
    C = Z
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'C', 'Z', exp_src_type=astroid.Assign, num_reasons=4)


def test_one_list():
    src = """
    L1 = [1, 2, 3]
    L1 = "Hello"
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'L1', str, exp_src_type=astroid.Assign, num_reasons=1)


def test_two_lists():
    src = """
    L1 = [1, 2, 3]
    L2 = ['a', 'b', 'c']
    L1 = L2
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'L1', 'L2', exp_src_type=astroid.Assign, num_reasons=2)


def test_tuple():
    src = """
    T1 = (1, 2)
    T2 = ('a', 'b')
    T1 = T2
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'T1', 'T2', exp_src_type=astroid.Assign, num_reasons=2)
