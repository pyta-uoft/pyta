from typing import List

import astroid
import pytest
import z3

from python_ta.transforms.z3_visitor import Z3Visitor

# test cases for arithmetic expressions
arithmetic_list = [
    """
    def f(x: int, y: int, z: float, a):
        '''
        Preconditions:
            - x ** 2 + y ** 2 == z ** 2
            - x > 0 and y > 0 and z == 0
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
    def in_empty_container(x: int):
        '''
        Preconditions:
            - x in []
            - x in set()
            - x in ()
        '''
        pass
    """,
    """
    def not_in_empty_container(x: int):
        '''
        Preconditions:
            - x not in []
            - x not in set()
            - x not in ()
        '''
        pass
    """,
]


# expected arithmetic expressions
x = z3.Int("x")
y = z3.Int("y")
z = z3.Real("z")
arithmetic_expected = [[x**2 + y**2 == z**2, z3.And([x > 0, y > 0, z == 0])]]

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
    [z3.BoolVal(False), z3.BoolVal(False)],
    [z3.BoolVal(True), z3.BoolVal(True)],
]

# lists of all test cases
code_list = [arithmetic_list, boolean_list, container_list]
expected_list = [arithmetic_expected, boolean_expected, container_expected]


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
