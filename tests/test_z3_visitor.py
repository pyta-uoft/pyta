import astroid
import z3

from python_ta.transforms.z3_visitor import Z3Visitor


def test_arithmetic_constraints():
    z3v = Z3Visitor()
    code = """
    def f(x: int, y: int, z: float, a):
        '''
        Preconditions:
            - x ** 2 + y ** 2 == z ** 2
            - x > 0 and y > 0 and z == 0
        '''
        pass
    """
    mod = z3v.visitor.visit(astroid.parse(code))
    function_def = mod.body[0]
    # Declare variables
    x = z3.Int("x")
    y = z3.Int("y")
    z = z3.Real("z")
    # Construct expected
    expected = [x**2 + y**2 == z**2, z3.And([x > 0, y > 0, z == 0])]
    actual = function_def.z3_constraints
    for e, a in zip(expected, actual):
        solver = z3.Solver()
        solver.add(e == a)
        assert solver.check() == z3.sat


def test_bool_constraints():
    z3v = Z3Visitor()
    code = """
    def f(x: bool, y: bool, z: bool, a):
        '''
        Preconditions:
            - x and y and z
            - not (x or y or z)
        '''
        pass
    """
    mod = z3v.visitor.visit(astroid.parse(code))
    function_def = mod.body[0]
    # Declare variables
    x = z3.Bool("x")
    y = z3.Bool("y")
    z = z3.Bool("z")
    # Construct expected
    expected = [z3.And([x, y, z]), z3.Not(z3.Or([x, y, z]))]
    actual = function_def.z3_constraints
    for e, a in zip(expected, actual):
        solver = z3.Solver()
        solver.add(e == a)
        assert solver.check() == z3.sat
