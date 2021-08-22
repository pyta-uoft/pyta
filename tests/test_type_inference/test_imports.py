from typing import Any

from astroid import nodes

from python_ta.typecheck.base import TypeFail

from .. import custom_hypothesis_support as cs


def test_imported_module_attribute():
    src = """
    import mod

    y = mod.x
    z = undefined_mod.x
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(nodes.Assign):
        if assgn_node.targets[0].name == "y":
            y = ti.lookup_typevar(assgn_node, "y")
            assert ti.type_constraints.resolve(y).getValue() == Any
        if assgn_node.targets[0].name == "z":
            assert isinstance(assgn_node.inf_type, TypeFail)


def test_imported_module_attribute_persists_any():
    src = """
    import mod

    y = mod.x
    y = 3
    z = mod.x
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(nodes.Assign):
        if assgn_node.targets[0].name == "z":
            z = ti.lookup_typevar(assgn_node, "z")
            assert ti.type_constraints.resolve(z).getValue() == Any


def test_from_import_variable():
    src = """
    from mod import x

    y = x
    z = w
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(nodes.Assign):
        if assgn_node.targets[0].name == "y":
            y = ti.lookup_typevar(assgn_node, "y")
            assert ti.type_constraints.resolve(y).getValue() == Any
        if assgn_node.targets[0].name == "z":
            assert isinstance(assgn_node.inf_type, TypeFail)


def test_from_import_attribute():
    src = """
    from mod import cls

    y = cls.x1
    z = undefined_cls.x2
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(nodes.Assign):
        if assgn_node.targets[0].name == "y":
            y = ti.lookup_typevar(assgn_node, "y")
            assert ti.type_constraints.resolve(y).getValue() == Any
        if assgn_node.targets[0].name == "z":
            assert isinstance(assgn_node.inf_type, TypeFail)


def test_imported_module_function():
    src = """
    import mod

    x = mod.func1(0, 1)
    y = mod.func1(0, 1) + 1
    undefined_mod.func2(0, 1)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        if call_node.func.attrname == "func1":
            assert call_node.inf_type.getValue() == Any
        if call_node.func.attrname == "func2":
            assert isinstance(call_node.inf_type, TypeFail)
    for assgn_node in ast_mod.nodes_of_class(nodes.Assign):
        if assgn_node.targets[0].name == "x":
            x = ti.lookup_typevar(assgn_node, "x")
            assert ti.type_constraints.resolve(x).getValue() == Any
        if assgn_node.targets[0].name == "y":
            y = ti.lookup_typevar(assgn_node, "y")
            assert ti.type_constraints.resolve(y).getValue() == int


def test_from_import_function():
    src = """
    from mod import func

    x = func(0, 1)
    y = func(0, 1) + 1
    undefined_func(0, 1)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for call_node in ast_mod.nodes_of_class(nodes.Call):
        if call_node.func.name == "func1":
            assert call_node.inf_type.getValue() == Any
        if call_node.func.name == "func2":
            assert isinstance(call_node.inf_type, TypeFail)
    for assgn_node in ast_mod.nodes_of_class(nodes.Assign):
        if assgn_node.targets[0].name == "x":
            x = ti.lookup_typevar(assgn_node, "x")
            assert ti.type_constraints.resolve(x).getValue() == Any
        if assgn_node.targets[0].name == "y":
            y = ti.lookup_typevar(assgn_node, "y")
            assert ti.type_constraints.resolve(y).getValue() == int
