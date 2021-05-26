"""
BinOp astroid node

A binary operation (like addition or division).

Attributes:
    - left   (Optional[Expr])
        - What is being applied to the operator on the left side.
    - op     (Optional[str])
        - The operator to be performed on left and right.
    - right  (Optional[Expr])
        - What is being applied to the operator on the right side.

Example 1:
    BinOp(
        op='+',
        left=Const(value=1),
        right=Const(value=2))

Examples of operators on primitive types; dunder function -> call and symbol:
    - __add__   -> +
    - __sub__   -> -
    - __mult__  -> *
    - __floordiv__  -> //
    - __mod__   -> %
    - __truediv__   -> /
    - __pow__   -> **

Refer to URL below for more information:
https://docs.python.org/3/library/operator.html?highlight=operator#module-operator

Type-checking:
    First, attempt to convert the left and right expression to a "common type" as per
    https://docs.python.org/3.6/reference/expressions.html?#arithmetic-conversions,
    Translate the operator into the corresponding method, and attempt to type-check
    the method call using the converted arguments.

    Otherwise, proceed as per
    https://docs.python.org/3.6/reference/datamodel.html#emulating-numeric-types
    Note that if both the calls to the standard method (e.g., '__add__') and the
    reflected method (e.g., '__radd__') fail to type-check, the failure corresponds
    to the method that was prioritized.
"""

1 + 2
a * b
4 - 8
8 ** 3
