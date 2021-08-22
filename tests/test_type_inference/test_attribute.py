from typing import *

from astroid import nodes
from pytest import skip

from python_ta.typecheck.base import TypeFail

from .. import custom_hypothesis_support as cs


def test_instance_dot_method():
    program = """
        class A:
            def foo(self, x):
                return x + 1

        A().foo(0)
        """
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(nodes.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_instance_dot_classmethod():
    program = """
        class A:
            @classmethod
            def foo(cls, x):
                return x + 1

        A().foo(0)
        """
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(nodes.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_instance_dot_staticmethod():
    program = """
        class A:
            @staticmethod
            def foo(x):
                return x + 1

        A().foo(0)
        """
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(nodes.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_class_dot_method():
    program = """
        class A:
            def foo(self, x):
                return x + 1

        A.foo(A(), 0)
        """
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(nodes.Attribute):
        assert (
            str(attribute_node.inf_type.getValue())
            == "typing.Callable[[ForwardRef('A'), int], int]"
        )


def test_class_dot_classmethod():
    program = """
        class A:
            @classmethod
            def foo(cls, x):
                return x + 1

        A.foo(0)
        """
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(nodes.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_class_dot_staticmethod():
    program = """
        class A:
            @staticmethod
            def foo(x):
                return x + 1

        A.foo(0)
        """
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(nodes.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_attribute_self_bind():
    """Make sure auto-binding of self persists"""
    program = """
        x = []
        f = x.append
        f(4)
        """
    module, ti = cs._parse_text(program, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node in module.nodes_of_class(nodes.AssignName)][0]
    assert str(ti.type_constraints.resolve(x).getValue()) == "typing.List[int]"


def test_subscript_attribute():
    program = """
        class A:
            def __init__(self):
                self.lst = []
                self.lst[0] = 1

        a = A()
        x = a.lst[0]
        """
    module, ti = cs._parse_text(program, reset=True)
    for assgn_node in module.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "x":
            x = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(x).getValue() == int


def test_obj_list_attribute():
    program = """
        class A:
            def __init__(self):
                self.name = 'abc'

        lst = [A(), A()]
        x = lst[0].name
        """
    module, ti = cs._parse_text(program, reset=True)
    for assgn_node in module.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "x":
            x = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(x).getValue() == str


def test_unknown_class_attribute():
    program = """
        def foo(a, x):
            y = x.name
            y = 3
            z = x.name
        """
    module, ti = cs._parse_text(program, reset=True)
    for assgn_node in module.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "z":
            z = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(z).getValue() == int


def test_unknown_class_attribute2():
    program = """
        def foo(x):
            return x.name + 2

        def bar(y):
            z = foo(y)
        """
    module, ti = cs._parse_text(program, reset=True)
    for binop_node in module.nodes_of_class(nodes.BinOp):
        assert binop_node.inf_type.getValue() == int
    for assgn_node in module.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "z":
            z = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(z).getValue() == int


def test_unknown_class_subscript_attribute():
    skip("Currently, the inferred type of the z variable is str")
    program = """
        def foo(x):
            return x.name[0]

        def bar(y):
            z = foo(y)
        """
    module, ti = cs._parse_text(program, reset=True)
    for assgn_node in module.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "z":
            z = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert isinstance(ti.type_constraints.resolve(z).getValue(), TypeVar)


def test_unknown_class_subscript_attribute2():
    program = """
        def foo(x):
            x.name[0] = 2
            return x.name[1]

        def bar(y):
            z = foo(y)
        """
    module, ti = cs._parse_text(program, reset=True)
    for assgn_node in module.nodes_of_class(nodes.AssignName):
        if assgn_node.name == "z":
            z = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(z).getValue() == int


def test_invalid_builtin_attribute():
    program = """
        x = 3
        y = x.name
        """
    module, ti = cs._parse_text(program, reset=True)
    assgn_node = list(module.nodes_of_class(nodes.Assign))[1]
    assert isinstance(assgn_node.inf_type, TypeFail)


def test_attribute_unification_fail():
    skip("This case is not supported yet")
    program = """
        class A:
            def __init__(self):
                self.name = 'abc'

        def f(x):
            x.name = 3

        a = A()
        f(a)
        f(A)
        """
    module, ti = cs._parse_text(program, reset=True)
    call_node1, call_node2 = module.nodes_of_class(nodes.Call)[1:]
    assert isinstance(call_node.inf_type1, TypeFail)
    assert isinstance(call_node.inf_type2, TypeFail)
