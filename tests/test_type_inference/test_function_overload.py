import astroid
from python_ta.transforms.type_inference_visitor import TypeInferer
from python_ta.typecheck.base import TypeInfo, TypeFail
from nose.tools import eq_


def test_overload_function():
    program = """
    def foo(x, y=None):
        return x + 5
        
    foo(5)
    foo(5, 6)
    """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)


def test_overload_function_2():
    program = """
    def foo(x, y=None, z=None):
        return x + 5

    foo(5)
    foo(5, 6)
    foo(5, 6, 7)
    foo(5, None, 7)
    """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)


def test_too_few_args():
    program = """
       def foo(x, y):
           return x + 5

       foo(5)
       """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type, TypeFail("Wrong number of arguments"))


def test_too_few_args_2():
    program = """
       def foo(x, y, z):
           return x + 5

       foo(5, 6)
       """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type, TypeFail("Wrong number of arguments"))


def test_too_many_args_2():
    program = """
       def foo(x, y):
           return x + 5

       foo(5, 6, 7)
       """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type, TypeFail("Wrong number of arguments"))


def test_too_many_args():
    program = """
       def foo(x):
           return x + 5

       foo(5, 6)
       """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type, TypeFail("Wrong number of arguments"))



def test_overload_function_with_annotations():
    program = """
    def foo(x: int, y: int=None):
        return x + 5

    foo(5)
    foo(5, 6)
    """
    ti = TypeInferer()
    ast_mod = astroid.parse(program)
    ti.environment_transformer().visit(ast_mod)
    ti.type_inference_transformer().visit(ast_mod)
    for call_node in ast_mod.nodes_of_class(astroid.Call):
        eq_(call_node.inf_type.getValue(), int)
