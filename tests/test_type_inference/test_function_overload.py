from typing import TypeVar

from astroid import nodes
from pytest import skip

from python_ta.typecheck.base import TypeFailFunction

from .. import custom_hypothesis_support as cs


def test_overload_function():
    program = """
    def foo(x, y=None):
        return x + 5

    foo(5)
    foo(5, 6)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert call_node.inf_type.getValue() == int


def test_overload_function_2():
    program = """
    def foo(x, y=None, z=None):
        return x + 5
    foo(5)
    foo(5, 6)
    foo(5, 6, 7)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert call_node.inf_type.getValue() == int


def test_overload_function_with_gap():
    program = """
    def foo(x, y=None, z=None):
        return x + 5
    foo(5, None, 7)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert call_node.inf_type.getValue() == int


def test_too_few_args():
    program = """
       def foo(x, y):
           return x + 5
       foo(5)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_few_args_2():
    program = """
       def foo(x, y, z):
           return x + 5
       foo(5, 6)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_many_args():
    program = """
       def foo(x):
           return x + 5
       foo(5, 6)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_many_args_2():
    program = """
       def foo(x, y):
           return x + 5
       foo(5, 6, 7)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_few_args_with_overload():
    program = """
       def foo(x, y, z=None):
           return x + 5
       foo(5)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_too_many_args_with_overload():
    program = """
       def foo(x, y=None):
           return x + 5
       foo(5, 6, 7)
       """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert isinstance(call_node.inf_type, TypeFailFunction)


def test_overload_function_with_annotations():
    program = """
    def foo(x: int, y: int=None):
        return x + 5
    foo(5)
    foo(5, 6)
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        assert call_node.inf_type.getValue() == int


def test_flagged_builtin_overload():
    program = """
    x = round(5.5)
    y = round(5.5, 1)
    """
    ast_mod, ti = cs._parse_text(program)
    for assgn_node in ast_mod.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "x":
            x = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(x).getValue() == int
        if assgn_node.name == "y":
            y = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(y).getValue() == float


def test_builtin_defaults():
    program = """
    x = range(1)
    y = range(1, 10)
    z = range(1, 10, 3)
    """
    ast_mod, ti = cs._parse_text(program)
    for assgn_node in ast_mod.nodes_of_class(nodes.AssignName):
        x = ti.lookup_typevar(assgn_node, assgn_node.name)
        assert ti.type_constraints.resolve(x).getValue() == range


def test_unresolved_builtin():
    skip("Requires proper handling of builtins with multiple signatures")
    program = """
    def f(x, y):
        return x + y

    z = f('abc', 'def')
    """
    ast_mod, ti = cs._parse_text(program)

    for assgn_node in ast_mod.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "z":
            z = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(z).getValue() == str


def test_unresolved_builtin2():
    skip("Requires proper handling of builtins with multiple signatures")
    program = """
    def f(x, y):
        return x + y

    def g(x, y):
        z = f(x, y)
        return z + 'abc'
    """
    ast_mod, ti = cs._parse_text(program)

    f_ret_node, g_ret_node = ast_mod.nodes_of_class(nodes.Return)
    assert isinstance(f_ret_node, TypeVar)
    assert g_ret_node.inf_type.getValue() == str
