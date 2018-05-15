import astroid
from typing import Any
from nose.tools import eq_
from python_ta.transforms.type_inference_visitor import TypeInferer
from python_ta.typecheck.base import TypeFail


def test_single_annotation_int():
    src = '''
    def foo(x: int):
        return x
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)


def test_single_annotation_str():
    src = '''
    def foo(x: str):
        return x
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), str)


def test_multiple_annotations():
    src = '''
    def foo(x: int, y: int):
        return x + y
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)
    eq_(ti.lookup_type(func_node, "y"), int)


def test_multiple_annotations_diff_type():
    src = '''
    def foo(x: int, y: str):
        print(y)
        return x
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)
    eq_(ti.lookup_type(func_node, "y"), str)


def test_call_wrong_type():
    src = '''
    def foo(x: int):
        return x
        
    foo("Hello")
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)

    call_node = next(ast_mod.nodes_of_class(astroid.Call))
    assert isinstance(call_node.inf_type, TypeFail)


def test_call_wrong_type_str():
    src = '''
    def foo(x: str):
        return x

    foo(5)
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), str)

    call_node = next(ast_mod.nodes_of_class(astroid.Call))
    assert isinstance(call_node.inf_type, TypeFail)


def test_call_multiple_annotation_wrong_type():
    src = '''
    def foo(x: int, y: str):
        return x

    foo("Hello", "Goodbye")
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)

    call_node = next(ast_mod.nodes_of_class(astroid.Call))
    assert isinstance(call_node.inf_type, TypeFail)


def test_mixed_annotation():
    src = '''
    def foo(x: int, y):
        return y

    foo(5, "Hello")
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)
    eq_(ti.lookup_type(func_node, "y"), Any)

    call_node = next(ast_mod.nodes_of_class(astroid.Call))
    eq_(call_node.inf_type.getValue(), Any)


def test_mixed_annotation_wrong():
    src = '''
    def foo(x: int, y):
        return y

    foo("Hello", 5)
    '''
    ti = TypeInferer()
    ast_mod = astroid.parse(src)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)

    func_node = next(ast_mod.nodes_of_class(astroid.FunctionDef))
    eq_(ti.lookup_type(func_node, "x"), int)
    eq_(ti.lookup_type(func_node, "y"), Any)

    call_node = next(ast_mod.nodes_of_class(astroid.Call))
    assert isinstance(call_node.inf_type, TypeFail)


