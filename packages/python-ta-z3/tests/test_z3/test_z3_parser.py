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


@pytest.mark.parametrize("a,b", itertools.product(range(-5, 5), [-3, -2, 2, 3]))
def test_apply_mod_op_matches_python(a, b) -> None:
    """Test that apply_mod_op method matches Python's modulo operation."""
    parser = Z3Parser()
    expected = a % b
    assert _value(parser.apply_mod_op(a, b)) == expected
    assert _value(parser.apply_mod_op(z3.IntVal(a), z3.IntVal(b))) == expected
    assert _value(parser.apply_mod_op(z3.IntVal(a), b)) == expected
    assert _value(parser.apply_mod_op(a, z3.IntVal(b))) == expected


def test_apply_mod_op_by_zero_is_unsatisfiable() -> None:
    """Test that applying modulo by zero returns an unsatisfiable formula."""
    parser = Z3Parser()
    assert z3.is_false(parser.apply_mod_op(5, 0))
    assert z3.is_false(parser.apply_mod_op(5, z3.IntVal(0)))


@pytest.mark.parametrize("a,b", itertools.product(range(-5, 5), [-3, -2, 2, 3]))
def test_apply_floordiv_op_matches_python(a, b) -> None:
    """Test that apply_floordiv_op method matches Python's floor division operation."""
    parser = Z3Parser()
    expected = a // b
    assert _value(parser.apply_floordiv_op(a, b)) == expected
    assert _value(parser.apply_floordiv_op(z3.IntVal(a), z3.IntVal(b))) == expected
    assert _value(parser.apply_floordiv_op(z3.IntVal(a), b)) == expected
    assert _value(parser.apply_floordiv_op(a, z3.IntVal(b))) == expected


def test_apply_floordiv_op_by_zero_is_unsatisfiable() -> None:
    """Test that applying floor division by zero returns an unsatisfiable formula."""
    parser = Z3Parser()
    assert z3.is_false(parser.apply_floordiv_op(5, 0))
    assert z3.is_false(parser.apply_floordiv_op(5, z3.IntVal(0)))


@pytest.mark.parametrize("operator", ["%", "//"])
def test_zero_divisor_comparison_is_unsatisfiable(operator) -> None:
    """Test that comparing an operation with a zero divisor returns false."""
    node = extract_node(f"x {operator} 0 == 2")
    parser = Z3Parser({"x": "int"})

    assert z3.is_false(parser.parse(node))


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
