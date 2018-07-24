import astroid
from nose.tools import eq_
from nose import SkipTest
from typing import *
import tests.custom_hypothesis_support as cs
from python_ta.typecheck.base import TypeInfo, TypeFail


def test_list():
    src = """
    *a, b = [1, 2, 3]
    a
    b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), List[int])
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), int)


def test_range():
    src = """
    *a, b = range(5)
    a
    b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), List[int])
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), int)


def test_tuple():
    src = """
    *a, b = (1, 2, 3)
    a
    b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), List[int])
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), int)


def test_order():
    src = """
    a, *b, c = [1, 2, 3, 4]
    a
    b
    c
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), int)
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), List[int])
        elif name_node.name == 'c':
            eq_(name_node.inf_type.getValue(), int)


def test_order_2():
    src = """
    a, *b = [1, 2, 3]
    a
    b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), int)
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), List[int])


def test_mixed_tuple():
    src = """
    *a, b = (1, "Hello", False)
    a
    b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), List[Any])
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), bool)


def test_mixed_tuple_order():
    src = """
    a, *b = (1, "Hello", False)
    a
    b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), int)
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), List[Any])


def test_mixed_tuple_three_var():
    src = """
    a, *b, c = (1, "Hello", False, "Goodbye", 4, "What")
    a
    b
    c
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), int)
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), List[Any])
        elif name_node.name == 'c':
            eq_(name_node.inf_type.getValue(), str)


def test_mixed_tuple_four_var():
    src = """
    a, *b, c, d = (1, "Hello", "Good morning", "Goodbye", 4, "What")
    a
    b
    c
    d
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for name_node in ast_mod.nodes_of_class(astroid.Name):
        assert not isinstance(name_node, TypeFail)
        if name_node.name == 'a':
            eq_(name_node.inf_type.getValue(), int)
        elif name_node.name == 'b':
            eq_(name_node.inf_type.getValue(), List[str])
        elif name_node.name == 'c':
            eq_(name_node.inf_type.getValue(), int)
        elif name_node.name == 'd':
            eq_(name_node.inf_type.getValue(), str)
