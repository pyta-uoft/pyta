import astroid
from typing import *
from typing import TupleMeta, CallableMeta, _ForwardRef
from python_ta.transforms.type_inference_visitor import main
from python_ta.typecheck.base import TypeConstraints, _TNode
from nose import SkipTest
from nose.tools import eq_

skip_msg = "Skipped"
error_msg = "Error"
tc = TypeConstraints()


# Helper functions
def unify_helper(arg1, arg2, exp_result):
    unify_result = tc.unify(arg1, arg2)
    if exp_result == error_msg:
        eq_(type(unify_result), str)
    else:
        eq_(unify_result, exp_result)


def setup_typevar(t: type):
    tn = _TNode(t)
    tv = tc.fresh_tvar(tn)
    tc.unify(tv, t)
    return tv


# Unify primitives
def test_same_prim():
    unify_helper(bool, bool, bool)
    unify_helper(int, int, int)
    unify_helper(str, str, str)


def test_diff_prim():
    unify_helper(bool, int, bool)
    unify_helper(bool, str, error_msg)
    unify_helper(int, str, error_msg)
    unify_helper(float, int, error_msg)


<<<<<<< HEAD
def test_diff_prim_flipped():
    raise SkipTest(skip_msg)
    # Simply returns the first argument, rather than the more specific one
    unify_helper(int, bool, bool)


=======
>>>>>>> 781def0664c8292033d90c1beb8c4948f027ee59
def test_int_bool():
    raise SkipTest(skip_msg)
    # base.py returns the first arg, rather than the subclass
    unify_helper(int, bool, bool)


# Unify TypeVars
def test_same_typevars():
    tc.reset()
    tv1 = setup_typevar(str)
    tv2 = setup_typevar(str)

    eq_(tc.resolve(tv1), str)
    eq_(tc.resolve(tv2), str)
    unify_helper(tv1, tv2, tv1)
    unify_helper(tv2, tv1, tv2)


def test_same_typevars_flipped():
    raise SkipTest(skip_msg)
    # unify only returns the first TypeVar, without resolving to concrete type
    tc.reset()
    tv1 = setup_typevar(str)
    tv2 = setup_typevar(str)

    unify_helper(tv1, tv2, tv2)
    unify_helper(tv2, tv1, tv1)


def test_diff_typevars():
    raise SkipTest(skip_msg)
    # unify raises excpetion in this case, rather than returning error string
    tc.reset()
    tv_str = setup_typevar(int)
    tv_int = setup_typevar(str)

    eq_(tc.resolve(tv_str), str)
    eq_(tc.resolve(tv_int), int)
    unify_helper(tv_int, tv_str, error_msg)


def test_one_typevar():
    tc.reset()
    tv = setup_typevar(str)

    eq_(tc.resolve(tv), str)
    unify_helper(tv, str, str)
    unify_helper(str, tv, str)
    unify_helper(tv, int, error_msg)
    unify_helper(int, tv, error_msg)


def test_one_typevar_bool_int():
    tc.reset()
    tv = setup_typevar(bool)

    eq_(tc.resolve(tv), bool)
    unify_helper(tv, int, bool)
    unify_helper(int, tv, bool)
    unify_helper(tv, str, error_msg)


# Unify ForwardRefs
def test_same_forward_ref():
    fr1 = _ForwardRef('a')
    fr2 = _ForwardRef('a')
    unify_helper(fr1, fr2, fr1)
    unify_helper(fr1, fr2, fr2)


def test_diff_forward_ref():
    fr1 = _ForwardRef('a')
    fr2 = _ForwardRef('b')
    unify_helper(fr1, fr2, error_msg)


def test_one_forward_ref():
    fr = _ForwardRef('a')
    unify_helper(fr, str, error_msg)


# Unify Tuples
def test_same_tuple():
    unify_helper(Tuple[int, int], Tuple[int, int], Tuple[int, int])
    unify_helper(Tuple[str, str], Tuple[str, str], Tuple[str, str])


def test_tuple_subclass():
    unify_helper(Tuple[bool, bool], Tuple[int, int], Tuple[bool, bool])


def test_tuple_subclass_flipped():
    raise SkipTest(skip_msg)
    # Should be returning Tuple[bool, bool], subclasses not returning in order
    unify_helper(Tuple[int, int], Tuple[bool, bool], Tuple[bool, bool])


def test_tuple_str():
    raise SkipTest(skip_msg)
    # _unify_generic not properly checking for error messages, instead attempts
    # to make invalid ForwardRef
    unify_helper(Tuple[int, int], Tuple[str, str], error_msg)


# Unify list
def test_same_list():
    unify_helper(List[str], List[str], List[str])
    unify_helper(List[int], List[int], List[int])


def test_diff_list():
    raise SkipTest(skip_msg)
    # _unify_generic not properly checking for error messages, instead attempts
    # to make invalid ForwardRef
    unify_helper(List[str], List[int], error_msg)


# Unify callables
def test_callable_subclass():
    c1 = Callable[[bool], bool]
    c2 = Callable[[int], int]

    eq_(tc.resolve(c1), Callable[[bool], bool])
    eq_(tc.resolve(c2), Callable[[int], int])
    unify_helper(c1, c2, c1)


def test_callable_subclass_flipped():
    raise SkipTest(skip_msg)
    # Should be returning Callable[[bool], bool]
    c1 = Callable[[bool], bool]
    c2 = Callable[[int], int]

    unify_helper(c2, c1, c1)


def test_diff_callable():
    raise SkipTest(skip_msg)
    # _unify_generic not properly checking for error messages, instead attempts
    # to make invalid ForwardRef
    c1 = Callable[[bool], bool]
    c2 = Callable[[str], str]

    unify_helper(c1, c2, error_msg)
