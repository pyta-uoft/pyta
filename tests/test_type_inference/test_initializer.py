import astroid
from typing import _ForwardRef
from python_ta.transforms.type_inference_visitor import TypeInferer
import tests.custom_hypothesis_support as cs
from python_ta.typecheck.base import TypeInfo, TypeFail
from nose.tools import eq_
from nose import SkipTest


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
            return 4

    foo = Foo()
    """
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type.getValue(), _ForwardRef)
        eq_(call_node.inf_type.getValue(), _ForwardRef('Foo'))


def test_class_with_multi_init():
    program = """
    class Foo:
    
        def __init__(self, x):
            self.a = x

    foo = Foo(5, 6)
    """

    # raise SkipTest("Should indicate that Foo() is called with the wrong number of arguments")
    ast_mod, ti = cs._parse_text(program)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        assert isinstance(call_node.inf_type.getValue(), _ForwardRef)
        eq_(call_node.inf_type.getValue(), _ForwardRef('Foo'))