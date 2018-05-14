import astroid
import tests.custom_hypothesis_support as cs
from python_ta.transforms.type_inference_visitor import TypeInferer
from python_ta.typecheck.base import TypeInfo, TypeFail
from nose.tools import eq_

src = '''
def foo(x, y=0, z=1):
    return (x + y) * z
    
a = foo(10)
b = foo(10, 5)
c = foo(10, 5, 12)
d = foo(5, 1, 2, 4)
'''


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
        assert not isinstance(call_node.inf_type, TypeFail)


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
        assert not isinstance(call_node.inf_type, TypeFail)


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


def test_too_many_args():
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
        assert isinstance(call_node.inf_type, TypeFail)

