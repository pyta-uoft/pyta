import astroid
from typing import _ForwardRef
import tests.custom_hypothesis_support as cs
from nose.tools import eq_
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
