from typing import *
from typing import TupleMeta, CallableMeta, _ForwardRef
# from python_ta.transforms.type_inference_visitor import main
from python_ta.typecheck.base import *
from python_ta.transforms.type_inference_visitor import main
from python_ta.typecheck.base import TypeConstraints
from nose import SkipTest
from nose.tools import eq_

skip_msg = "Skipped"
error_msg = "Error"
tc = TypeConstraints()


# Helper functions
def unify_helper(arg1, arg2, exp_result):
    unify_result = tc.unify(TypeInfo(arg1), TypeInfo(arg2))
    if exp_result == error_msg:
        assert isinstance(unify_result, TypeFail)  # TODO: check for error messages
        eq_(type(unify_result), str)  # TODO: check for error messages
    elif isinstance(exp_result, TypeVar):
        eq_(unify_result, TypeInfo(tc.resolve(exp_result)))
    else:
        eq_(unify_result, TypeInfo(exp_result))


def setup_typevar(t: type):
    tv = tc.fresh_tvar(None)
    tc.unify(TypeInfo(tv), TypeInfo(t))
    tc.unify(tv, t)
    return tv


# Unify primitives
def test_same_prim():
    unify_helper(bool, bool, bool)
    unify_helper(int, int, int)
    unify_helper(str, str, str)


def test_diff_prim():
    unify_helper(bool, str, error_msg)
    unify_helper(int, str, error_msg)
    unify_helper(bool, int, error_msg)
    unify_helper(float, int, error_msg)
    unify_helper(float, str, error_msg)


def test_subclasses():
    raise SkipTest(skip_msg)
    # Currently no support for subclasses
    unify_helper(int, bool, bool)
    unify_helper(bool, int, bool)


# Unify TypeVars
def test_same_typevars():
    tc.reset()
    tv1 = setup_typevar(str)
    tv2 = setup_typevar(str)

    eq_(tc.resolve(tv1), str)
    eq_(tc.resolve(tv2), str)
    unify_helper(tv1, tv2, tv1)


def test_same_typevars_flipped():
    tc.reset()
    tv1 = setup_typevar(str)
    tv2 = setup_typevar(str)

    eq_(tc.resolve(tv1), str)
    eq_(tc.resolve(tv2), str)
    unify_helper(tv1, tv2, tv2)


def test_diff_typevars():
    tc.reset()
    tv_str = setup_typevar(str)
    tv_int = setup_typevar(int)

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
    raise SkipTest("skip_msg")
    # Currently no support for subclasses
    tc.reset()
    tv = setup_typevar(bool)

    eq_(tc.resolve(tv), bool)
    unify_helper(tv, int, bool)
    unify_helper(int, tv, bool)
    unify_helper(tv, str, error_msg)


def test_two_typevar():
    tc.reset()
    tv1 = setup_typevar(bool)
    tv2 = tc.fresh_tvar(None)
    unify_helper(tv1, tv2, bool)


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
    raise SkipTest(skip_msg)
    # Currently no support for subclasses
    unify_helper(Tuple[bool, bool], Tuple[int, int], Tuple[bool, bool])
    unify_helper(Tuple[int, int], Tuple[bool, bool], Tuple[bool, bool])


def test_diff_tuple():
    raise SkipTest(skip_msg)
    # _unify_generic not properly checking for error messages, instead attempts
    # to make invalid ForwardRef
    unify_helper(Tuple[int, int], Tuple[str, str], error_msg)


def test_nested_tuples():
    unify_helper(Tuple[str, Tuple[str, bool]], Tuple[str, Tuple[str, bool]],
                 Tuple[str, Tuple[str, bool]])


def test_typevars_tuple():
    tv1 = tc.fresh_tvar(None)
    tv2 = tc.fresh_tvar(None)
    unify_helper(Tuple[tv1, tv2], Tuple[str, bool], Tuple[str, bool])
    eq_(tc.resolve(tv1), str)
    eq_(tc.resolve(tv2), bool)


def test_typevars_nested_tuples():
    raise SkipTest('resolve needs to be recursive for this test to work')
    t1 = tc.fresh_tvar(None)
    t2 = Tuple[tv1, bool]
    unify_helper(tv2, Tuple[Tuple[str, bool], bool],
                 Tuple[Tuple[str, bool], bool])
    eq_(tc.resolve(tv1), Tuple[str, bool])
    eq_(tc.resolve(tv2), Tuple[Tuple[str, bool], bool])


def test_diff_nested_tuples():
    raise SkipTest('error propagation must be implemented for this to work')
    unify_helper(Tuple[str, Tuple[str, str]],
                 Tuple[str, Tuple[bool, str]], error_msg)


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
def test_same_callable():
    tc.reset()
    c1 = Callable[[bool], bool]
    c2 = Callable[[bool], bool]

    eq_(tc.resolve(c1), Callable[[bool], bool])
    eq_(tc.resolve(c2), Callable[[bool], bool])
    unify_helper(c1, c2, c1)
    unify_helper(c1, c2, c2)
    unify_helper(c2, c1, c1)
    unify_helper(c2, c1, c2)


def test_callable_subclass():
    raise SkipTest(skip_msg)
    # No support for subclasses
    c1 = Callable[[bool], bool]
    c2 = Callable[[int], int]

    eq_(tc.resolve(c1), Callable[[bool], bool])
    eq_(tc.resolve(c2), Callable[[int], int])
    unify_helper(c1, c2, c1)
    unify_helper(c2, c1, c1)


def test_diff_callable():
    raise SkipTest(skip_msg)
    # _unify_generic not properly checking for error messages, instead attempts
    # to make invalid ForwardRef
    c1 = Callable[[bool], bool]
    c2 = Callable[[str], str]

    unify_helper(c1, c2, error_msg)
