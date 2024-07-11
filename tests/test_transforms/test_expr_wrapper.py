"""Tests for ExprWrapper in python_ta.transforms."""

from astroid import parse

from python_ta.transforms import ExprWrapper, Z3ParseException


def test_expr_wrapper_invalid_node() -> None:
    exception_caught = False

    try:
        ExprWrapper(None)
    except Z3ParseException:
        exception_caught = True

    assert exception_caught


def test_expr_wrapper_assignment() -> None:
    assignment = "n = x + y - z"

    mod = parse(assignment)
    node = mod.body[0]

    expr = ExprWrapper(node)
    assert expr.node is node.value
