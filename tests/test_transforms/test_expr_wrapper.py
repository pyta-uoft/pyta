"""Tests for ExprWrapper in python_ta.transforms."""

from python_ta.transforms import ExprWrapper, Z3ParseException


def test_expr_wrapper_invalid_node():
    exception_caught = False

    try:
        ExprWrapper(None)
    except Z3ParseException:
        exception_caught = True

    assert exception_caught
