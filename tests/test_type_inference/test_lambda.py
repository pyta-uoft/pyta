from .. import custom_hypothesis_support as cs
from pytest import skip

import astroid
from python_ta.typecheck.base import TypeInfo, TypeFail


def test_lambda_simple_call():
    src = """
    y = (lambda x: x + 1)(0)
    z = (lambda x: x + 'def')('abc')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for lambda_node in ast_mod.nodes_of_class(astroid.Lambda):
        assert str(lambda_node.inf_type.getValue()) == 'typing.Callable[[int], int]' or \
               str(lambda_node.inf_type.getValue()) == 'typing.Callable[[str], str]'
    for var_node in ast_mod.nodes_of_class(astroid.AssignName):
        if var_node.name == 'y':
            y = ti.lookup_typevar(var_node, 'y')
            assert ti.type_constraints.resolve(y).getValue() == int
        if var_node.name == 'z':
            y = ti.lookup_typevar(var_node, 'z')
            assert ti.type_constraints.resolve(y).getValue() == str


def test_lambda_simple_call_invalid():
    src = """
    y = (lambda x: x + 1)('abc')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFail)


def test_define_fn_lambda():
    src = """
    f = lambda x: x + 1
    y = f(0)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for var_node in ast_mod.nodes_of_class(astroid.AssignName):
        if var_node.name == 'y':
            y = ti.lookup_typevar(var_node, 'y')
            assert ti.type_constraints.resolve(y).getValue() == int


def test_define_fn_lambda_invalid():
    src = """
    f = lambda x: x + 1
    x = f('abc')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFail)


def test_lambda_polymorphic_simple():
    src = """
    f = lambda x: x
    y = f('abc')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for lambda_node in ast_mod.nodes_of_class(astroid.Lambda):
        x = ti.lookup_inf_type(lambda_node, 'x').getValue()
        assert str(lambda_node.inf_type.getValue()) == f'typing.Callable[[{x}], {x}]'
    for var_node in ast_mod.nodes_of_class(astroid.AssignName):
        if var_node.name == 'y':
            y = ti.lookup_typevar(var_node, 'y')
            assert ti.type_constraints.resolve(y).getValue() == str


def test_lambda_polymorphic_builtin_lookup():
    skip('This requires proper handling of unresolved calls to'
                   'builtin methods with multiple variants')
    src = """
    f = lambda x, y: x + y
    y = f('abc', 'def')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for lambda_node in ast_mod.nodes_of_class(astroid.Lambda):
        assert str(lambda_node.inf_type.getValue()) == 'typing.Callable[[~_T0, ~_T0], ~_T0]'
    for var_node in ast_mod.nodes_of_class(astroid.AssignName):
        if var_node.name == 'y':
            y = ti.lookup_typevar(var_node, 'y')
            assert ti.type_constraints.resolve(y).getValue() == str


def test_lambda_constant():
    src = """
    x = lambda: 1
    y = x()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for var_node in ast_mod.nodes_of_class(astroid.AssignName):
        if var_node.name == 'x':
            x = ti.lookup_typevar(var_node, 'x')
            assert str(ti.type_constraints.resolve(x).getValue()) == 'typing.Callable[[], int]'
        if var_node.name == 'y':
            x = ti.lookup_typevar(var_node, 'y')
            assert ti.type_constraints.resolve(x).getValue() == int


def test_nested_lambda():
    src = """
    f = lambda x: (lambda y: x + y)
    g = f(0)
    y = g(0)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for var_node in ast_mod.nodes_of_class(astroid.AssignName):
        if var_node.name == 'f':
            f = ti.lookup_typevar(var_node, 'f')
            assert str(ti.type_constraints.resolve(f).getValue()) == \
                   'typing.Callable[[int], typing.Callable[[int], int]]'
        if var_node.name == 'g':
            g = ti.lookup_typevar(var_node, 'g')
            assert str(ti.type_constraints.resolve(g).getValue()) == \
                   'typing.Callable[[int], int]'
        if var_node.name == 'y':
            y = ti.lookup_typevar(var_node, 'y')
            assert ti.type_constraints.resolve(y).getValue() == int

