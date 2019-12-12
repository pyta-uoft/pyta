import astroid
from typing import List


from hypothesis import given, settings, assume, HealthCheck
from .. import custom_hypothesis_support as cs
from python_ta.typecheck.errors import BINOP_TO_METHOD
from python_ta.typecheck.base import TypeFail, TypeFailFunction
settings.load_profile("pyta")


@given(cs.binop_node())
@settings(suppress_health_check=[HealthCheck.too_slow, HealthCheck.filter_too_much])
def test_binop_non_bool_concrete(node):
    """Test type setting of BinOp node(s) with non-boolean operands."""
    module, inferer = cs._parse_text(node)
    binop_node = list(module.nodes_of_class(astroid.BinOp))[0]
    left_type, right_type = binop_node.left.inf_type.getValue(), binop_node.right.inf_type.getValue()
    exp_func_type = inferer.type_store.lookup_method(BINOP_TO_METHOD[node.op], left_type, right_type, node=binop_node)
    if not isinstance(exp_func_type, TypeFailFunction):
        exp_return_type = exp_func_type.__args__[-1]
    else:
        exp_return_type = None
    assume(exp_return_type is not None)
    assert binop_node.inf_type.getValue() == exp_return_type


def test_binop_reverse():
    src = """
    x = 3 * [1,2,3]
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == List[int]


def test_binop_autoconvert():
    program = """
    x = 1 + 1.0
    y = 1 + 1j
    z = 1.0 + 1j
    """
    module, inferer = cs._parse_text(program, reset=True)
    x, y, z = [inferer.lookup_typevar(node, node.name) for node
               in module.nodes_of_class(astroid.AssignName)]
    assert inferer.type_constraints.resolve(x).getValue() == float
    assert inferer.type_constraints.resolve(y).getValue() == complex
    assert inferer.type_constraints.resolve(z).getValue() == complex


def test_binop_autoconvert_fail():
    program = """
    x = 1 << 1.0
    y = 1.0 << 1
    z = 1j % 2j
    w = 1j << 2
    """
    module, inferer = cs._parse_text(program, reset=True)
    for binop_node in module.nodes_of_class(astroid.BinOp):
        assert isinstance(binop_node.inf_type, TypeFail)


def test_binop_userdefn():
    src = """
    class A:
        def __add__(self, i):
            return 1

        def __radd__(self, i):
            return 1.0

    class B:
        def __add__(self, i):
            return 'abc'

        def __radd__(self, i):
            return True

    a = A()
    b = B()
    x = a + b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    a, b, x = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)][8:]
    assert ti.type_constraints.resolve(x).getValue() == int


def test_binop_reverse_userdefn():
    src = """
    class A:
        def __radd__(self, i):
            return 1.0

    class B:
        def __add__(self, i):
            return 'abc'

        def __radd__(self, i):
            return True

    a = A()
    b = B()
    x = a + b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    a, b, x = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)][6:]
    assert ti.type_constraints.resolve(x).getValue() == bool


def test_binop_reverse_right_subclasses_left():
    src = """
    class A:
        def __add__(self, i):
            return 1
            
        def __radd__(self, i):
            return 1.0
            
    class B(A):
        def __add__(self, i):
            return 'abc'
    
        def __radd__(self, i):
            return [1]
            
    a = A()
    b = B()
    x = a + b
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    a, b, x = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)][8:]
    assert ti.type_constraints.resolve(x).getValue() == List[int]
