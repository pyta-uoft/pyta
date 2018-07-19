import astroid
import tests.custom_hypothesis_support as cs
from nose.tools import eq_
from python_ta.typecheck.base import TypeFailFunction


def test_overload_function():
    program = """
    def foo(x, y=None):
        return x + 5

    foo(5)
    foo(5, 6)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)


def test_overload_function_2():
    program = """
    def foo(x, y=None, z=None):
        return x + 5
    foo(5)
    foo(5, 6)
    foo(5, 6, 7)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)


def test_overload_function_with_gap():
    program = """
    def foo(x, y=None, z=None):
        return x + 5
    foo(5, None, 7)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)


def test_too_few_args():
    program = """
       def foo(x, y):
           return x + 5
       foo(5)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_few_args_2():
    program = """
       def foo(x, y, z):
           return x + 5
       foo(5, 6)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_many_args():
    program = """
       def foo(x):
           return x + 5
       foo(5, 6)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_many_args_2():
    program = """
       def foo(x, y):
           return x + 5
       foo(5, 6, 7)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_few_args_with_overload():
    program = """
       def foo(x, y, z=None):
           return x + 5
       foo(5)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_many_args_with_overload():
    program = """
       def foo(x, y=None):
           return x + 5
       foo(5, 6, 7)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_overload_function_with_annotations():
    program = """
    def foo(x: int, y: int=None):
        return x + 5
    foo(5)
    foo(5, 6)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)
