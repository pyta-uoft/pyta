import nose
from nose import SkipTest
import astroid
from typing import *
from typing import _ForwardRef
import tests.custom_hypothesis_support as cs


def test_instance_dot_method():
    program = \
        '''
        class A:
            def foo(self, x):
                return x + 1

        A().foo(0)
        '''
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(astroid.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_instance_dot_classmethod():
    program = \
        '''
        class A:
            @classmethod
            def foo(cls, x):
                return x + 1

        A().foo(0)
        '''
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(astroid.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_instance_dot_staticmethod():
    program = \
        '''
        class A:
            @staticmethod
            def foo(x):
                return x + 1

        A().foo(0)
        '''
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(astroid.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_class_dot_method():
    program = \
        '''
        class A:
            def foo(self, x):
                return x + 1

        A.foo(A(), 0)
        '''
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(astroid.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[_ForwardRef('A'), int], int]"


def test_class_dot_classmethod():
    program = \
        '''
        class A:
            @classmethod
            def foo(cls, x):
                return x + 1

        A.foo(0)
        '''
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(astroid.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_class_dot_staticmethod():
    program = \
        '''
        class A:
            @staticmethod
            def foo(x):
                return x + 1

        A.foo(0)
        '''
    module, _ = cs._parse_text(program, reset=True)
    for attribute_node in module.nodes_of_class(astroid.Attribute):
        assert str(attribute_node.inf_type.getValue()) == "typing.Callable[[int], int]"


def test_attribute_self_bind():
    """Make sure auto-binding of self persists"""
    program = \
        '''
        x = []
        f = x.append
        f(4)
        '''
    module, ti = cs._parse_text(program, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in module.nodes_of_class(astroid.AssignName)][0]
    assert str(ti.type_constraints.resolve(x).getValue()) == "typing.List[int]"
