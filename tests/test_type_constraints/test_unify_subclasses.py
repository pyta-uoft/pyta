from typing import *
from typing import TupleMeta, CallableMeta, _ForwardRef
from python_ta.typecheck.base import *
from python_ta.transforms.type_inference_visitor import main
from python_ta.typecheck.base import TypeConstraints
from nose import SkipTest
from nose.tools import eq_
from nose import SkipTest
from nose.tools import eq_
from test_unify import unify_helper, resolve_helper, setup_typevar

skip_msg = "Skipped"
error_msg = "Error"
tc = TypeConstraints()

raise SkipTest(skip_msg)


def test_subclasses():
    unify_helper(int, bool, bool)
    unify_helper(bool, int, bool)


def test_one_typevar_bool_int():
    tc.reset()
    tv = setup_typevar(bool)

    resolve_helper(tv, bool)
    unify_helper(tv, int, bool)
    unify_helper(int, tv, bool)
    unify_helper(tv, str, error_msg)


def test_tuple_subclass():
    unify_helper(Tuple[bool, bool], Tuple[int, int], Tuple[bool, bool])
    unify_helper(Tuple[int, int], Tuple[bool, bool], Tuple[bool, bool])


def test_callable_subclass():
    c1 = Callable[[bool], bool]
    c2 = Callable[[int], int]

    unify_helper(c1, c2, c1)
    unify_helper(c2, c1, c1)
