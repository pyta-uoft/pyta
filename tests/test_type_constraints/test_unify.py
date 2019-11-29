from typing import *
from typing import Callable, ForwardRef
from python_ta.typecheck.base import TypeResult, TypeInfo, TypeFail, TypeConstraints, create_Callable
from pytest import skip


skip_msg = "Skipped"
tc = TypeConstraints()


# Helper functions
def unify_helper(arg1: type, arg2: type, exp_result: Union[type, TypeFail]):
    unify_result = TypeInfo(arg1) >> (
        lambda t1: TypeInfo(arg2) >> (
            lambda t2: tc.unify(t1, t2)))
    if isinstance(exp_result, TypeFail):
        assert isinstance(unify_result, TypeFail)
    else:
        assert tc.resolve(unify_result.getValue()).getValue() == tc.resolve(exp_result).getValue()


def setup_typevar(t: type):
    tv = tc.fresh_tvar(None)
    tc.unify(tv, t)
    return tv


def resolve_helper(t: type, exp_type: type):
    assert tc.resolve(t).getValue() == exp_type


# Unify primitives
def test_same_prim():
    unify_helper(bool, bool, bool)
    unify_helper(int, int, int)
    unify_helper(str, str, str)


def test_diff_prim():
    unify_helper(bool, str, TypeFail(
        f'Incompatible Types {bool} and {str}'))
    unify_helper(int, str, TypeFail(
        f'Incompatible Types {int} and {str}'))
    unify_helper(bool, int, TypeFail(
        f'Incompatible Types {bool} and {int}'))
    unify_helper(float, int, TypeFail(
        f'Incompatible Types {float} and {int}'))
    unify_helper(float, str, TypeFail(
        f'Incompatible Types {float} and {str}'))


# Unify TypeVars
def test_same_typevars():
    tc.reset()
    tv1 = setup_typevar(str)
    tv2 = setup_typevar(str)

    resolve_helper(tv1, str)
    resolve_helper(tv2, str)

    unify_helper(tv1, tv2, tv1)


def test_same_typevars_flipped():
    tc.reset()
    tv1 = setup_typevar(str)
    tv2 = setup_typevar(str)

    resolve_helper(tv1, str)
    resolve_helper(tv2, str)
    unify_helper(tv1, tv2, tv2)


def test_diff_typevars():
    tc.reset()
    tv_str = setup_typevar(str)
    tv_int = setup_typevar(int)

    resolve_helper(tv_str, str)
    resolve_helper(tv_int, int)
    unify_helper(tv_int, tv_str, TypeFail(
        f'Incompatible Types {str} and {int}'))


def test_one_typevar():
    tc.reset()
    tv = setup_typevar(str)

    resolve_helper(tv, str)
    unify_helper(tv, str, str)
    unify_helper(str, tv, str)
    unify_helper(tv, int, TypeFail(
        f'Incompatible Types {str} and {int}'))
    unify_helper(int, tv, TypeFail(
        f'Incompatible Types {int} and {str}'))


def test_two_typevar():
    tc.reset()
    tv1 = setup_typevar(bool)
    tv2 = tc.fresh_tvar(None)
    unify_helper(tv1, tv2, bool)


# Unify ForwardRefs
def test_same_forward_ref():
    fr1 = ForwardRef('a')
    fr2 = ForwardRef('a')
    unify_helper(fr1, fr2, fr1)
    unify_helper(fr1, fr2, fr2)


def test_diff_forward_ref():
    skip('The existing error msg does not apply to this situation')
    fr1 = ForwardRef('a')
    fr2 = ForwardRef('b')
    unify_helper(fr1, fr2, TypeFail("Attempted to unify forwardref  with non-ref"))


def test_one_forward_ref():
    fr = ForwardRef('a')
    unify_helper(fr, str, TypeFail("Attempted to unify forwardref  with non-ref"))


# Unify Tuples
def test_same_tuple():
    unify_helper(Tuple[int, int], Tuple[int, int], Tuple[int, int])
    unify_helper(Tuple[str, str], Tuple[str, str], Tuple[str, str])


def test_diff_tuple():
    unify_helper(Tuple[int, int], Tuple[str, str], TypeFail(
        f'Incompatible Types {Tuple[int, int]} and {Tuple[str, str]}'))


def test_nested_tuples():
    unify_helper(Tuple[str, Tuple[str, bool]], Tuple[str, Tuple[str, bool]],
                 Tuple[str, Tuple[str, bool]])


def test_typevars_tuple():
    tv1 = tc.fresh_tvar(None)
    tv2 = tc.fresh_tvar(None)
    unify_helper(Tuple[tv1, tv2], Tuple[str, bool], Tuple[str, bool])
    resolve_helper(tv1, str)
    resolve_helper(tv2, bool)


def test_typevars_nested_tuples():
    tv1 = tc.fresh_tvar(None)
    tv2 = Tuple[tv1, bool]
    unify_helper(tv2, Tuple[Tuple[str, bool], bool],
                 Tuple[Tuple[str, bool], bool])
    resolve_helper(tv1, Tuple[str, bool])
    resolve_helper(tv2, Tuple[Tuple[str, bool], bool])


def test_diff_nested_tuples():
    unify_helper(Tuple[str, Tuple[str, str]],
                 Tuple[str, Tuple[bool, str]], TypeFail(
                     f'Incompatible Types {Tuple[str, Tuple[str, str]]} and {Tuple[str, Tuple[bool, str]]}'))


# Unify list
def test_same_list():
    unify_helper(List[str], List[str], List[str])
    unify_helper(List[int], List[int], List[int])


def test_diff_list():
    unify_helper(List[str], List[int], TypeFail(
        f'Incompatible Types {List[str]} and {List[int]}'))


# Unify callables
def test_same_callable():
    tc.reset()
    c1 = Callable[[bool], bool]
    c2 = Callable[[bool], bool]

    unify_helper(c1, c2, c1)
    unify_helper(c1, c2, c2)
    unify_helper(c2, c1, c1)
    unify_helper(c2, c1, c2)


def test_diff_callable():
    c1 = Callable[[bool], bool]
    c2 = Callable[[str], str]

    unify_helper(c1, c2, TypeFail(
        f'Incompatible Types {c1} and {c2}'))


# Polymorphic types
def test_simple_polymorphic_call():
    tc.reset()
    tv1 = tc.fresh_tvar()
    tv2 = tc.fresh_tvar()
    fn1 = create_Callable([tv1, tv2], bool, {tv1, tv2})
    fn2 = create_Callable([int, int], bool)

    unify_helper(fn1, fn2, Callable[[int, int], bool])


def test_higher_order_polymorphic_call():
    tc.reset()
    tv1 = tc.fresh_tvar()
    tv2 = tc.fresh_tvar()

    fn0 = create_Callable([tv1, int], int, {tv1})
    fn1 = create_Callable([int, int], int)

    fn2 = create_Callable([fn0, int], bool)
    fn3 = create_Callable([fn1, int], bool)
    fn4 = create_Callable([tv2, int], bool, {tv2})

    unify_helper(fn2, fn3, Callable[[Callable[[int, int], int], int], bool])
    unify_helper(fn2, fn4, Callable[[Callable[[int, int], int], int], bool])

    resolve_helper(tv1, int)
    resolve_helper(tv2, Callable[[int, int], int])


# Union types
def test_simple_union():
    tc.reset()
    unify_helper(int, Union[int, str], int)


def test_tvar_union():
    tc.reset()
    unify_helper(tc.fresh_tvar(), Union[int, str], Union[int, str])
    unify_helper(Union[int, str], tc.fresh_tvar(), Union[int, str])


def test_two_unions():
    tc.reset()
    unify_helper(Union[int, str, None], Union[bool, int], int)


def test_optional():
    tc.reset()
    tv1 = tc.fresh_tvar()

    unify_helper(int, Optional[int], int)
    unify_helper(type(None), Optional[int], type(None))
    unify_helper(tv1, Optional[int], Optional[int])
