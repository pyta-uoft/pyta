from typing import Tuple

from astroid import nodes

from python_ta.transforms.type_inference_visitor import NoType
from python_ta.typecheck.base import TypeFail, TypeInfo

from .. import custom_hypothesis_support as cs
from ..custom_hypothesis_support import lookup_type


def generate_tuple(length: int, t: type = None):
    program = ""
    for i in range(length + 1):
        if t is None:
            program += f"x{i}, "
        elif t == int:
            program += f"{i}, "
        elif t == bool:
            program += f"{i % 2 == 0}, "
        elif t == str:
            program += f"'{str(chr(i+97))}', "
    return program


def generate_tuple_assign(length: int, t: type, same_length: bool, more_args: bool = None):
    program = ""
    for i in range(1, length):
        for j in range(1, length):
            if same_length and i == j:
                program += generate_tuple(i) + "= " + generate_tuple(j, t) + "\n"
            elif not same_length:
                if (more_args and i > j) or (not more_args and i < j):
                    program += generate_tuple(i) + "= " + generate_tuple(j, t) + "\n"
    return program


def test_tuple_same_length_int():
    program = generate_tuple_assign(10, int, True)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert assign_node.inf_type == NoType()


def test_tuple_same_length_bool():
    program = generate_tuple_assign(10, bool, True)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert assign_node.inf_type == NoType()


def test_tuple_same_length_str():
    program = generate_tuple_assign(10, str, True)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert assign_node.inf_type == NoType()


def test_tuple_single_var():
    program = """
    a = 1, 2
    b = 1, 2, 3
    c = 1, 2, 3, 4
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert assign_node.inf_type == NoType()


def test_tuple_single_val():
    program = """
    a, b = 1
    a, b, c = 1
    a, b, c, d = 1
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)


def test_tuple_extra_vars():
    program = generate_tuple_assign(10, int, False, True)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)


def test_tuple_extra_value():
    program = generate_tuple_assign(10, int, False, False)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)


def test_tuple_subscript():
    program = """
    lst = ['Hello', 'Goodbye']
    lst[0], lst[1] = 'Bonjour', 'Au revoir'
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert not isinstance(assign_node.inf_type, TypeFail)


def test_tuple_attribute():
    program = """
    class A:
        def __init__(self):
            self.first_attr = 0
            self.second_attr = 1

    a = A()
    a.first_attr, a.second_attr = 10, 11
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert not isinstance(assign_node.inf_type, TypeFail)


def test_tuple_attribute_variable():
    program = """
    class A:
        def __init__(self):
            self.first_attr = 0
            self.second_attr = 1

    a = A()
    some_list = [1, 2]

    a.first_attr, a.second_attr = some_list
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(nodes.Assign):
        assert not isinstance(assign_node.inf_type, TypeFail)


def test_tuple_empty():
    program = """
    def f(x):
        a = ()
        b = (x,)
        a = b
    """
    module, ti = cs._parse_text(program)
    functiondef_node = next(module.nodes_of_class(nodes.FunctionDef))
    assert lookup_type(ti, functiondef_node, "a") == Tuple[()]
    x_type = lookup_type(ti, functiondef_node, "x")
    assert lookup_type(ti, functiondef_node, "b") == Tuple[x_type]
