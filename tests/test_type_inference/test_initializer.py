import astroid
from typing import _ForwardRef
import tests.custom_hypothesis_support as cs
from nose.tools import eq_
from nose import SkipTest
from python_ta.transforms.type_inference_visitor import TypeFail


def test_class_with_init():
    program = """
    class Foo:
    
        def __init__(self):
            self.a = 5
    
    foo = Foo()
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type.getValue(), _ForwardRef)
        eq_(call_node.inf_type.getValue(), _ForwardRef('Foo'))


def test_class_without_init():
    program = """
    class Foo:
        def fee(self):
            return 1

    foo = Foo()
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type.getValue(), _ForwardRef)
        eq_(call_node.inf_type.getValue(), _ForwardRef('Foo'))


def test_wrong_number_init():
    program = """
    class Foo:
        def __init__(self, x):
            self.a = x

    foo = Foo()
    """
    ast_mod, ti = cs._parse_text(program, True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFail)


def test_class_defined_later():
    program = """
    class A:
        def __init__(self):
            self.attr = B()

    class B:
        pass
    """
    ast_mod, ti = cs._parse_text(program, True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert not isinstance(call_node.inf_type, TypeFail)


def test_builtin_overloaded_initializers():
    program = """
    range1 = range(10)
    range2 = range(1, 10, 1)
    """
    ast_mod, ti = cs._parse_text(program, True)
    for assgn_node in ast_mod.nodes_of_class(astroid.AssignName):
        if assgn_node.name == 'range1':
            range1 = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(range1).getValue() == range
        if assgn_node.name == 'range2':
            range2 = ti.lookup_typevar(assgn_node, assgn_node.name)
            assert ti.type_constraints.resolve(range2).getValue() == range


def test_init_defined_later():
    program = """
    a = A('Hello')
    
    class A:
        def __init__(self, x):
            self.attr = x
    """
    ast_mod, ti = cs._parse_text(program, True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert not isinstance(call_node.inf_type, TypeFail)


def test_wrong_number_init_defined_later():
    program = """
    a = A('Hello')
    
    class A:
        def __init__(self):
            pass
    """
    raise SkipTest("Initializers for classes that have not yet been visited will accept any number of arguments")
    ast_mod, ti = cs._parse_text(program, True)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type, TypeFail)
