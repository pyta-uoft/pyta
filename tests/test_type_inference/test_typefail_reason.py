import astroid
import tests.custom_hypothesis_support as cs
from typing import *
from python_ta.typecheck.base import TypeFail, TypeFailUnify, TypeFailFunction
from tests.test_type_inference.test_tnode_structure import find_type_fail
from nose.tools import eq_


def verify_typefail_unify(tf: TypeFailUnify, exp_tn1, exp_tn2, exp_src_type):
    assert isinstance(tf, TypeFailUnify)
    for tn, exp_r in zip([tf.tnode1, tf.tnode2], [exp_tn1, exp_tn2]):
        if tn.ast_node and hasattr(tn.ast_node, 'name'):
            eq_(tn.ast_node.name, exp_r)
        else:
            eq_(tn.type, exp_r)
    assert isinstance(tf.src_node, exp_src_type)


def verify_typefail_function(tf: TypeFailUnify, exp_func_type):
    assert isinstance(tf, TypeFailFunction)
    eq_(tf.func_tnode.type, exp_func_type)


def test_var_assign():
    src = """
    A = 1
    A = 'One'
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'A', str, astroid.Assign)

    reasons = tf.get_reasons()
    assert int in reasons


def test_two_var_assign():
    src = """
    A = 1
    B = 'Two'
    A = B
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'A', 'B', astroid.Assign)

    reasons = tf.get_reasons()
    assert int in reasons
    assert str in reasons


def test_one_list():
    src = """
    L = [1, 2, 3]
    L = "Hello"
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'L', str, astroid.Assign)

    reasons = tf.get_reasons()
    assert List[int] in reasons


def test_two_lists():
    src = """
    L = [1, 2, 3]
    L = ['One', 'Two', 'Three']
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'L', List[str], astroid.Assign)

    reasons = tf.get_reasons()
    assert List[int] in reasons


def test_tuple():
    src = """
    T = (1, 2)
    T = 'Hello'
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'T', str, astroid.Assign)

    reasons = tf.get_reasons()
    assert Tuple[int, int] in reasons


def test_two_tuple():
    src = """
    T = (1, 2)
    T = ('One', 'Two')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'T', Tuple[str, str], astroid.Assign)

    reasons = tf.get_reasons()
    assert Tuple[int, int] in reasons


def test_mixed_tuple():
    src = """
    T = (1, 2)
    T = (3, "Four")
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_unify(tf, 'T', Tuple[int, str], astroid.Assign)

    reasons = tf.get_reasons()
    assert Tuple[int, int] in reasons


def test_function():
    src = """
    def f(x):
        return x + 1
        
    f('Hello')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_function(tf, Callable[[int], int])


def test_multiple_functions():
    src = """
    def f(x):
        return x + 1
    
    def g(x):
        return x + 2

    f('Hello')
    g('Goodbye')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tf = find_type_fail(ast_mod).inf_type
    verify_typefail_function(tf, Callable[[int], int])

    reasons = tf.get_reasons()
    assert isinstance(reasons[-1], astroid.FunctionDef)
    eq_(reasons[-1].name, 'f')

