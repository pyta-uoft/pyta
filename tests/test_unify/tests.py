import astroid
from typing import *
from typing import TupleMeta, CallableMeta, _ForwardRef
from python_ta.transforms.type_inference_visitor import  main
from python_ta.typecheck.base import TypeConstraints, _TNode
from nose import SkipTest

# SkipTest documentation http://nose.readthedocs.io/en/latest/plugins/skip.html

# TODO Should this be moved into a separate setup function?
skip_msg = "Skipped"
tc = TypeConstraints()

## Unify primitives
# TODO These functions return 'type', should they return the individual type itself?
# If not, how to more specifically check value of return type?
def test_unify_bool():
    assert isinstance((tc.unify(bool,bool)), type)

def test_unify_str():
    assert isinstance((tc.unify(str,str)), type)

def test_unify_bool_int():
    assert isinstance((tc.unify(bool, int)), type)

def test_unify_int_bool():
    assert isinstance((tc.unify(int, bool)), type)

def test_unify_bool_str():
    #print(tc.unify(bool,str))
    assert isinstance((tc.unify(bool,str)), str)

def test_unify_int_str():
    assert isinstance((tc.unify(int,str)), str)

## Unify TypeVars
def test_unify_two_typevars():
    tn1 = _TNode(str)
    tvar1 = tc.fresh_tvar(tn1)
    tc.unify(tvar1, str)

    tn2 = _TNode(str)
    tvar2 = tc.fresh_tvar(tn2)
    tc.unify(tvar2, str)

    assert tc.resolve(tvar1) == str
    assert tc.resolve(tvar2) == str
    assert isinstance(tc.unify(tvar1, tvar2), TypeVar)

def test_unify_two_typevars_wrong_types():
    raise SkipTest(skip_msg)
    # This test currently raises a TypeInferenceError through the _merge_sets function_name
    # Should be returning error message instead

    tn1 = _TNode(str)
    tvar_str = tc.fresh_tvar(tn1)
    tc.unify(tvar_str, str)

    tn2 = _TNode(int)
    tvar_int = tc.fresh_tvar(tn2)
    tc.unify(tvar_int, int)

    assert tc.resolve(tvar_str) == str
    assert tc.resolve(tvar_int) == int
    assert isinstance(tc.unify(tvar_str, tvar_int), str)

def test_unify_two_typevars_bools():
    # This test currently raises a TypeInferenceError through the _merge_sets function_name
    # Should be returning error message instead

    tn1 = _TNode(bool)
    tvar1 = tc.fresh_tvar(tn1)
    tc.unify(tvar1, bool)

    tn2 = _TNode(bool)
    tvar2 = tc.fresh_tvar(tn2)
    tc.unify(tvar2, bool)

    assert tc.resolve(tvar1) == bool
    assert tc.resolve(tvar2) == bool

    assert tc.resolve(tvar1) == bool
    assert tc.resolve(tvar2) == bool
    assert isinstance(tc.unify(tvar1, tvar2), TypeVar)

def test_unify_one_typevar():
    tn1 = _TNode(str)
    tvar_str = tc.fresh_tvar(tn1)
    tc.unify(tvar_str, str)

    assert tc.resolve(tvar_str) == str
    assert isinstance(tc.unify(tvar_str, str), type)

def test_unify_one_typevar_wrong_type():
    tn1 = _TNode(str)
    tvar_str = tc.fresh_tvar(tn1)
    tc.unify(tvar_str, str)

    assert tc.resolve(tvar_str) == str
    assert isinstance(tc.unify(tvar_str, int), str)

def test_unify_one_typevar_wrong_type_flipped():
    tn1 = _TNode(str)
    tvar_str = tc.fresh_tvar(tn1)
    tc.unify(tvar_str, str)

    assert tc.resolve(tvar_str) == str
    assert isinstance(tc.unify(int, tvar_str), str)

## Unify ForwardRefs
def test_unify_forwardref():
    fr1 = _ForwardRef('a')
    fr2 = _ForwardRef('a')
    assert isinstance(tc.unify(fr1, fr2), _ForwardRef)

def test_unify_forwardref_wrong_type():
    fr1 = _ForwardRef('a')
    fr2 = _ForwardRef('b')
    assert isinstance(tc.unify(fr1, fr2), str)

# TODO Shouldn't this result in delaying checking the forwardref until later?
def test_unify_forwardref_str():
    fr1 = _ForwardRef('a')
    assert isinstance(tc.unify(fr1, str), str)

## Unify tuples
def test_unify_tuple_int():
    assert isinstance(tc.unify(Tuple[int,int], Tuple[int,int]), TupleMeta)

def test_unify_tuple_str():
    assert isinstance(tc.unify(Tuple[str,str], Tuple[str,str]), TupleMeta)

def test_unify_tuple_bool_int():
    assert isinstance(tc.unify(Tuple[bool,bool], Tuple[int,int]), type(Tuple[bool,bool]))
    assert isinstance(tc.unify(Tuple[bool,bool], Tuple[int,int]), TupleMeta)

def test_unify_tuple_str_int():
    raise SkipTest(skip_msg)
    # should return error message
    assert isinstance(tc.unify(Tuple[str,int], Tuple[int,int]), str)

## Unify lists
def test_unify_list_str():
    assert isinstance(tc.unify(List[str], List[str]), type)

def test_unify_list_str_int():
    raise SkipTest(skip_msg)
    # should return error message
    assert isinstance(tc.unify(List[str], List[int]), str)

## Unify callables
def test_unify_callable_bool_int():
    c1 = Callable[[bool], bool]
    c2 = Callable[[int], int]
    assert isinstance(tc.unify(c1, c2), CallableMeta)
    assert isinstance(tc.unify(c1, c2), type(c1))

def test_unify_callable_bool_str():
    raise SkipTest(skip_msg)
    # should return error message
    c1 = Callable[[bool], bool]
    c2 = Callable[[str], str]
    assert isinstance(tc.unify(c1, c2), str)
