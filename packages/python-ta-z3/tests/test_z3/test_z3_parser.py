"""Tests for Z3Parser in python_ta_z3."""

import itertools

import pytest
import z3
from astroid import extract_node
from python_ta_z3.z3_parser import Z3ParseException, Z3Parser


def test_z3_parser_assignment() -> None:
    assignment = "n = 2 + 3"

    node = extract_node(assignment)
    parser = Z3Parser()
    assert parser.parse(node) == 5


def _value(z3_expr: int | z3.ExprRef) -> int:
    """Convert a Z3 expression to a Python integer."""
    return z3.simplify(z3_expr).as_long() if z3.is_int(z3_expr) else z3_expr


def _is_unsat(*formulas: z3.BoolRef) -> bool:
    """Check if the conjunction of the given formulas is unsatisfiable."""
    solver = z3.Solver()
    solver.add(*formulas)
    return solver.check() == z3.unsat


@pytest.mark.parametrize("a,b", itertools.product(range(-5, 5), [-3, -2, 2, 3]))
def test_apply_mod_op_matches_python(a, b) -> None:
    """Test that apply_mod_op method matches Python's modulo operation."""
    parser = Z3Parser()
    expected = a % b
    assert _value(parser.apply_mod_op(a, b)) == expected
    assert _value(parser.apply_mod_op(z3.IntVal(a), z3.IntVal(b))) == expected
    assert _value(parser.apply_mod_op(z3.IntVal(a), b)) == expected
    assert _value(parser.apply_mod_op(a, z3.IntVal(b))) == expected


@pytest.mark.parametrize("a,b", itertools.product(range(-5, 5), [-3, -2, 2, 3]))
def test_apply_floordiv_op_matches_python(a, b) -> None:
    """Test that apply_floordiv_op method matches Python's floor division operation."""
    parser = Z3Parser()
    expected = a // b
    assert _value(parser.apply_floordiv_op(a, b)) == expected
    assert _value(parser.apply_floordiv_op(z3.IntVal(a), z3.IntVal(b))) == expected
    assert _value(parser.apply_floordiv_op(z3.IntVal(a), b)) == expected
    assert _value(parser.apply_floordiv_op(a, z3.IntVal(b))) == expected


@pytest.mark.parametrize("method_name", ["apply_mod_op", "apply_floordiv_op"])
@pytest.mark.parametrize("zero", [0, z3.IntVal(0)])
def test_zero_divisor_records_unsatisfiable_constraint(method_name, zero):
    """Test that applying modulo or floor division with a zero divisor records an unsatisfiable constraint."""
    parser = Z3Parser()
    getattr(parser, method_name)(5, zero)
    assert len(parser.parsing_constraints) == 1
    assert _is_unsat(*parser.parsing_constraints)


@pytest.mark.parametrize("operator", ["//", "%"])
@pytest.mark.parametrize("rhs", [0, 2])
def test_zero_divisior_comparison_is_unsatisfiable(operator, rhs) -> None:
    """Test that comparison with a zero divisor is unsatisfiable."""
    node = extract_node(f"x {operator} 0 == {rhs}")
    parser = Z3Parser({"x": "int"})
    expr = parser.parse(node)
    assert _is_unsat(expr, *parser.parsing_constraints)


@pytest.mark.parametrize(
    "left,right",
    [
        (z3.Real("r"), 2),  # real operand
        (2.5, 2),  # python float
        ("abc", 2),  # string
    ],
)
def test_apply_mod_floordiv_reject_non_ints(left, right) -> None:
    """Test that applying modulo and floor division to non-integer operands raises a Z3ParseException."""
    parser = Z3Parser()
    for method in (parser.apply_mod_op, parser.apply_floordiv_op):
        with pytest.raises(Z3ParseException):
            method(left, right)
