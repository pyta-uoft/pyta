from typing import List

import astroid
import pytest
import z3

from python_ta.transforms.z3_visitor import Z3Visitor


def _get_constraints_from_code(code) -> List[z3.ExprRef]:
    """
    Return the z3 constraints of the given function
    """
    z3v = Z3Visitor()
    mod = z3v.visitor.visit(astroid.parse(code))
    function_def = mod.body[0]
    return function_def.z3_constraints


def test_arithmetic_constraints():
    code = """
    def f(x: int, y: int, z: float, a):
        '''
        Preconditions:
            - x ** 2 + y ** 2 == z ** 2
            - x > 0 and y > 0 and z == 0
        '''
        pass
    """
    # Declare variables
    x = z3.Int("x")
    y = z3.Int("y")
    z = z3.Real("z")
    # Construct expected
    expected = [x**2 + y**2 == z**2, z3.And([x > 0, y > 0, z == 0])]
    actual = _get_constraints_from_code(code)
    for e, a in zip(expected, actual):
        solver = z3.Solver()
        solver.add(e == a)
        assert solver.check() == z3.sat


def test_bool_constraints():
    code = """
    def f(x: bool, y: bool, z: bool, a):
        '''
        Preconditions:
            - x and y and z
            - not (x or y or z)
        '''
        pass
    """
    # Declare variables
    x = z3.Bool("x")
    y = z3.Bool("y")
    z = z3.Bool("z")
    # Construct expected
    expected = [z3.And([x, y, z]), z3.Not(z3.Or([x, y, z]))]
    actual = _get_constraints_from_code(code)
    for e, a in zip(expected, actual):
        solver = z3.Solver()
        solver.add(e == a)
        assert solver.check() == z3.sat


def test_container_constraints():
    code_list = [
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
    def not_in_list(x: int):
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
    # Declare variables
    x = z3.Int("x")
    # Construct expected
    expected_list = [
        [z3.Or(x == 1, x == 2, x == 3)],
        [z3.Or(x == 1, x == 2, x == 3)],
        [z3.Or(x == 1, x == 2, x == 3)],
        [z3.And(x != 1, x != 2, x != 3)],
        [z3.And(x != 1, x != 2, x != 3)],
        [z3.And(x != 1, x != 2, x != 3)],
        [z3.BoolVal(False), z3.BoolVal(False)],
        [z3.BoolVal(True), z3.BoolVal(True)],
    ]

    for expected, code in zip(expected_list, code_list):
        actual = _get_constraints_from_code(code)
        assert len(actual) == len(expected)

        @pytest.mark.parametrize("expected, actual", zip(expected, actual))
        def check_constraint(expected, actual):
            solver = z3.Solver()
            solver.add(expected == actual)
            assert solver.check() == z3.sat

        for expected, actual in zip(expected, actual):
            check_constraint(expected, actual)
