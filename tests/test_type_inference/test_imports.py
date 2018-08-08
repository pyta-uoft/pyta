import astroid
import tests.custom_hypothesis_support as cs
from python_ta.typecheck.base import TypeVar, TypeFail


def test_imported_module_attribute():
    src = """
    import mod
    
    y = mod.x
    z = undefined_mod.x
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(astroid.Assign):
        if assgn_node.targets[0].name == 'y':
            y = ti.lookup_typevar(assgn_node, 'y')
            assert isinstance(ti.type_constraints.resolve(y).getValue(), TypeVar)
        if assgn_node.targets[0].name == 'z':
            assert isinstance(assgn_node.inf_type, TypeFail)


def test_from_import_variable():
    src = """
    from mod import x
    
    y = x
    z = w
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(astroid.Assign):
        if assgn_node.targets[0].name == 'y':
            y = ti.lookup_typevar(assgn_node, 'y')
            assert isinstance(ti.type_constraints.resolve(y).getValue(), TypeVar)
        if assgn_node.targets[0].name == 'z':
            assert isinstance(assgn_node.inf_type, TypeFail)


def test_from_import_attribute():
    src = """
    from mod import cls
    
    y = cls.x1
    z = undefined_cls.x2
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(astroid.Assign):
        if assgn_node.targets[0].name == 'y':
            y = ti.lookup_typevar(assgn_node, 'y')
            assert isinstance(ti.type_constraints.resolve(y).getValue(), TypeVar)
        if assgn_node.targets[0].name == 'z':
            assert isinstance(assgn_node.inf_type, TypeFail)


def test_imported_module_function():
    src = """
    import mod

    mod.func1(0, 1)
    undefined_mod.func2(0, 1)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        if call_node.func.attrname == 'func1':
            assert isinstance(call_node.inf_type.getValue(), TypeVar)
        if call_node.func.attrname == 'func2':
            assert isinstance(call_node.inf_type, TypeFail)


def test_from_import_function():
    src = """
    from mod import func

    func(0, 1)
    undefined_func(0, 1)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        if call_node.func.name == 'func1':
            assert isinstance(call_node.inf_type.getValue(), TypeVar)
        if call_node.func.name == 'func2':
            assert isinstance(call_node.inf_type, TypeFail)


def test_imported_function_delayed_return_resolution():
    src = """
    from mod import func
    
    y = func(0, 1)
    z = y + 3
    w = func(1, 2)
    u = func('abc', 'def')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    for assgn_node in ast_mod.nodes_of_class(astroid.Assign):
        if assgn_node.targets[0].name == 'y':
            y = ti.lookup_typevar(assgn_node, 'y')
            assert ti.type_constraints.resolve(y).getValue() == int
        if assgn_node.targets[0].name == 'w':
            w = ti.lookup_typevar(assgn_node, 'w')
            assert ti.type_constraints.resolve(w).getValue() == int
        if assgn_node.targets[0].name == 'u':
            assert isinstance(assgn_node.inf_type, TypeFail)
