from typing import List

import astroid
import pytest
import z3

from python_ta.cfg import ControlFlowGraph
from python_ta.transforms.z3_visitor import Z3Visitor

# test cases for z3 variables
z3_vars_example = """
def f(x: int, y: float, z: bool, a: str):
    '''
    This is a function to test z3 vars
    '''
    n = x + y - z
"""

# test cases for arithmetic expressions
arithmetic_list = [
    """
    def f(x: int, y: int, z: float, a):
        '''
        Preconditions:
            - x ** 2 + y ** 2 == z ** 2
            - x > 0 and y > 0 and z == 0
            - x + y != z
        '''
        pass
    """
]

# test cases for boolean expressions
boolean_list = [
    """
    def f(x: bool, y: bool, z: bool, a):
        '''
        Preconditions:
            - x and y and z
            - not (x or y or z)
        '''
        pass
    """
]

# test cases for container (list/set/tuple) expressions
container_list = [
    """
    def in_list(x: int):
        '''
        Preconditions:
            - x in [1, 2, 3]
        '''
        pass
    """,
    """
    def in_set(x: int):
        '''
        Preconditions:
            - x in {1, 2, 3}
        '''
        pass
    """,
    """
    def in_tuple(x: int):
        '''
        Preconditions:
            - x in (1, 2, 3)
        '''
        pass
    """,
    """
    def not_in_list(x: int):
        '''
        Preconditions:
            - x not in [1, 2, 3]
        '''
        pass
    """,
    """
    def not_in_set(x: int):
        '''
        Preconditions:
            - x not in {1, 2, 3}
        '''
        pass
    """,
    """
    def not_in_tuple(x: int):
        '''
        Preconditions:
            - x not in (1, 2, 3)
        '''
        pass
    """,
    """
    def in_empty_list(x: int):
        '''
        Preconditions:
            - x in []
        '''
        pass
    """,
    """
    def in_empty_tuple(x: int):
        '''
        Preconditions:
            - x in ()
        '''
        pass
    """,
    """
    def not_in_empty_list(x: int):
        '''
        Preconditions:
            - x not in []
        '''
        pass
    """,
    """
    def not_in_empty_tuple(x: int):
        '''
        Preconditions:
            - x not in ()
        '''
        pass
    """,
]

# test cases for strings expressions
string_list = [
    """
    def string_equality(x: str, y: str, z: str):
        '''
        Preconditions:
            - x == y
            - z == x + y
            - x != z
        '''
        pass
    """,
    """
    def in_string(x: str, y: str):
        '''
        Preconditions:
            - x in "abc"
            - x in y
        '''
        pass
    """,
    """
    def not_in_string(x: str, y: str):
        '''
        Preconditions:
            - x not in "abc"
            - x not in y
        '''
        pass
    """,
    """
    def string_indexing_positive(x: str, y: str):
        '''
        Preconditions:
            - x[0] == y
            - x[1] == "a"
        '''
        pass
    """,
    """
    def string_indexing_negative(x: str, y: str):
        '''
        Preconditions:
            - x[-1] == "b"
            - x[-2] == y
        '''
        pass
    """,
    """
    def string_slicing_positive(x: str, y: str, z: str):
        '''
        Preconditions:
            - x[1:4] == y
            - x[4:5] == "a"
            - x[4:] == "abc"
            - x[:3] == "def"
            - x[:] == z
        '''
        pass
    """,
    """
    def string_slicing_negative(x: str, y: str, z: str):
        '''
        Preconditions:
            - x[-4:-1] == y
            - x[-4:-3] == "a"
            - x[-4:] == "abc"
            - x[:-3] == "def"
        '''
        pass
    """
    """
    def string_step_length(x: str, y: str):
        '''
        Preconditions:
            - x[1:5:2] == y
            - x[:5:4] == "ab"
            - x[6:3:-2] == "cd"
        '''
        pass
    """,
]


# expected arithmetic expressions
x = z3.Int("x")
y = z3.Int("y")
z = z3.Real("z")
arithmetic_expected = [[x**2 + y**2 == z**2, z3.And([x > 0, y > 0, z == 0]), x + y != z]]

# expected boolean expressions
x = z3.Bool("x")
y = z3.Bool("y")
z = z3.Bool("z")
boolean_expected = [[z3.And([x, y, z]), z3.Not(z3.Or([x, y, z]))]]

# expected container expressions
x = z3.Int("x")
container_expected = [
    [z3.Or(x == 1, x == 2, x == 3)],
    [z3.Or(x == 1, x == 2, x == 3)],
    [z3.Or(x == 1, x == 2, x == 3)],
    [z3.And(x != 1, x != 2, x != 3)],
    [z3.And(x != 1, x != 2, x != 3)],
    [z3.And(x != 1, x != 2, x != 3)],
    [z3.BoolVal(False)],
    [z3.BoolVal(False)],
    [z3.BoolVal(True)],
    [z3.BoolVal(True)],
]

# expected string expressions
x = z3.String("x")
y = z3.String("y")
z = z3.String("z")
string_expected = [
    [x == y, z == x + y, x != z],
    [z3.Contains("abc", x), z3.Contains(y, x)],
    [z3.Not(z3.Contains("abc", x)), z3.Not(z3.Contains(y, x))],
    [
        z3.SubString(x, 0, 1) == y,
        z3.SubString(x, 1, 1) == "a",
    ],
    [
        z3.SubString(x, z3.Length(x) - 1, 1) == "b",
        z3.SubString(x, z3.Length(x) - 2, 1) == y,
    ],
    [
        z3.SubString(x, 1, 3) == y,
        z3.SubString(x, 4, 1) == "a",
        z3.SubString(x, 4, z3.Length(x) - 4) == "abc",
        z3.SubString(x, 0, 3) == "def",
        x == z,
    ],
    [
        z3.SubString(x, z3.Length(x) - 4, 3) == y,
        z3.SubString(x, z3.Length(x) - 4, 1) == "a",
        z3.SubString(x, z3.Length(x) - 4, 4) == "abc",
        z3.SubString(x, 0, z3.Length(x) - 3) == "def",
    ],
    [
        z3.Concat(z3.SubString(x, 1, 1), z3.SubString(x, 3, 1)) == y,
        z3.Concat(z3.SubString(x, 0, 1), z3.SubString(x, 4, 1)) == "ab",
        z3.Concat(z3.SubString(x, 6, 1), z3.SubString(x, 4, 1)) == "cd",
    ],
]

# lists of all test cases
code_list = [arithmetic_list, boolean_list, container_list, string_list]
expected_list = [arithmetic_expected, boolean_expected, container_expected, string_expected]


def _get_constraints_from_code(code) -> List[z3.ExprRef]:
    """
    Return the z3 constraints of the given function
    """
    z3v = Z3Visitor()
    mod = z3v.visitor.visit(astroid.parse(code))
    function_def = mod.body[0]
    return function_def.z3_constraints


@pytest.mark.parametrize("code, expected", zip(code_list, expected_list))
def test_constraint(code, expected):
    for function, function_expected in zip(code, expected):
        function_actual = _get_constraints_from_code(function)
        assert len(function_actual) == len(function_expected)
        for a, e in zip(function_actual, function_expected):
            solver = z3.Solver()
            solver.add(a == e)
            assert solver.check() == z3.sat


# test cases for invalid inputs
#
# Explanation on unhandled_slicing_index:
#   a string slicing operation with indeterminanat upper bound
#   (such as the variable's lnegth) and a step length not equal
#   to 1 is currently not supported.
invalid_input_list = [
    """
    def invalid_in_op_type(x: int, y: bool):
        '''
        Preconditions:
            - x in y
        '''
        pass
    """,
    """
    def invalid_string_index(x: str, a):
        '''
        Preconditions:
            - x[a] == "a"
        '''
        pass
    """,
    """
    def invalid_slicing_index(x: str, a, b, c):
        '''
        Preconditions:
            - x[a:b:c] == "a"
        '''
        pass
    """,
    """
    def invalid_subscript_type(x: int):
        '''
        Preconditions:
            - x[1] == 0
        '''
        pasd
    """,
    """
    def unhandled_slicing_index(x: str):
        '''
        Preconditions:
            - x[::2] == "abc"
            - x[::-2] == "abc"
        '''
        pass
    """,
]


@pytest.mark.parametrize("invalid_code", invalid_input_list)
def test_invalid_input(invalid_code):
    assert _get_constraints_from_code(invalid_code) == []


def test_cfg_z3_vars_initialization():
    """
    Test that the cfg's z3 variable mapping is correctly initialized.
    """
    node = astroid.extract_node(z3_vars_example)

    cfg = ControlFlowGraph()
    cfg.add_arguments(node.args)

    assert len(cfg._z3_vars) == 4
    assert cfg._z3_vars["x"] == z3.Int("x")
    assert cfg._z3_vars["y"] == z3.Real("y")
    assert cfg._z3_vars["z"] == z3.Bool("z")
    assert cfg._z3_vars["a"] == z3.String("a")
