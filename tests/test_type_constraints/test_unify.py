from typing import *
import astroid
import nose
from nose.tools import eq_
from nose.tools import nottest
from python_ta.typecheck.base import TypeConstraints


def test_unify_typevar_concrete():
    tc = TypeConstraints()
    tvar = tc.fresh_tvar(None)
    res = tc.unify(tvar, bool)
    eq_(res, bool)
    eq_(tc.resolve(tvar), bool)

def test_unify_two_typevar_concrete():
    tc = TypeConstraints()
    tvar1 = tc.fresh_tvar(None)
    tc.unify(tvar1, bool)
    res = tc.unify(tvar1, bool)
    tvar2 = tc.fresh_tvar(None)
    res = tc.unify(tvar1, tvar2)
    eq_(res, bool)
    eq_(tc.resolve(tvar2), bool)

def test_unify_nested_tuples():
    tc = TypeConstraints()
    res = tc.unify(Tuple[str, Tuple[str, bool]], Tuple[str, Tuple[str, bool]])
    eq_(res, Tuple[str, Tuple[str, bool]])

def test_unify_typevars_in_tuple():
    tc = TypeConstraints()
    tvar1 = tc.fresh_tvar(None)
    tvar2 = tc.fresh_tvar(None)
    res = tc.unify(Tuple[tvar1, tvar2], Tuple[str, bool])
    eq_(res, Tuple[str, bool])
    eq_(tc.resolve(tvar1), str)
    eq_(tc.resolve(tvar2), bool)

@nottest
def test_unify_typevars_nested_tuples():
    tc = TypeConstraints()
    tvar1 = tc.fresh_tvar(None)
    tvar2 = Tuple[tvar1, bool]
    res = tc.unify(tvar2, Tuple[Tuple[str, bool], bool])
    eq_(res, Tuple[Tuple[str, bool], bool])
    eq_(tc.resolve(tvar1), Tuple[str, bool])
    eq_(tc.resolve(tvar2), Tuple[Tuple[str, bool], bool])


# error cases

def test_diff_concrete_types():
    tc = TypeConstraints()
    eq_(tc.unify(str, bool),
        'Incompatible types <class \'str\'> <class \'bool\'>')

def test_diff_nested_tuples():
    tc = TypeConstraints()
    res = tc.unify(Tuple[str, Tuple[str, str]], Tuple[str, Tuple[bool, str]])
    eq_(res, 'Incompatible types <class \'str\'> <class \'bool\'>')
