import astroid
from nose.tools import eq_
import tests.custom_hypothesis_support as cs
from python_ta.transforms.type_inference_visitor import NoType
from python_ta.typecheck.base import TypeInfo, TypeFail


def generate_tuple(length: int, t: type=None):
    program = ''
    for i in range(length + 1):
        if t is None:
            program += f'x{i}, '
        elif t == int:
            program += f'{i}, '
        elif t == bool:
            program += f'{i % 2 == 0}, '
        elif t == str:
            program += f'\'{str(chr(i+97))}\', '
    return program


def generate_tuple_assign(length: int, same_length: bool, more_args: bool = None):
    program = ''
    type_list = [int, bool, str]
    for t in type_list:
        for i in range(1, length):
            for j in range(1, length):
                if same_length and i == j:
                    program += generate_tuple(i) + '= ' + generate_tuple(j, t) + '\n'
                elif not same_length:
                    if (more_args and i > j) or (not more_args and i < j):
                        program += generate_tuple(i) + '= ' + generate_tuple(j, t) + '\n'
    return program


def test_tuple_same_length():
    program = generate_tuple_assign(10, True)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        eq_ (assign_node.inf_type, TypeInfo(NoType))


def test_tuple_single_var():
    program = """
    a = 1, 2
    b = 1, 2, 3
    c = 1, 2, 3, 4
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)
        eq_(assign_node.inf_type, TypeFail("Cannot assign multiple values to single variable"))


def test_tuple_single_val():
    program = """
    a, b = 1
    a, b, c = 1
    a, b, c, d = 1
    """
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)
        eq_(assign_node.inf_type, TypeFail("Cannot assign single value to multiple variables"))


def test_tuple_extra_vars():
    program = generate_tuple_assign(10, False, True)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)
        eq_(assign_node.inf_type, TypeFail("Too many variables in assignment node"))


def test_tuple_extra_value():
    program = generate_tuple_assign(10, False, False)
    module, _ = cs._parse_text(program)
    for assign_node in module.nodes_of_class(astroid.Assign):
        assert isinstance(assign_node.inf_type, TypeFail)
        eq_(assign_node.inf_type, TypeFail("Too many values in assignment node"))

