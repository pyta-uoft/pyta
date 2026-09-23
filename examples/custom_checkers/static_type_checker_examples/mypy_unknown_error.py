"""
Triggers a mypy error that is not included in PythonTA's supported list.
It is used in test_ignores_unknown_message_error_code from the test_static_type_checker module.

The triggered error has the code func-returns-value, which indicates that a function return value
with a type annotation of None was not ignored.

Mypy documentation: https://mypy.readthedocs.io/en/stable/error_code_list.html#check-that-called-function-returns-a-value-func-returns-value
"""


def f() -> None:
    """A function that returns None."""
    return None


if f():  # This raises a func-returns-value error, since f() has a return type annotation of None
    x = 1
