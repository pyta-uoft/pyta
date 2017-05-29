"""
BinOp astroid node

A binary operation (like addition or division).

Attributes:
    - left   (Expr)
        - Any expression node.
    - right  (Expr)
        - Any expression node.
    - op     (Expr)
        - The operator to be performed on left and right.

Example:
    - left   -> Name(Num(n=1), ctx=Load())
    - right  -> Name(Num(n=2), ctx=Load())
    - op     -> Add()

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
"""

1 + 2
a * b
4 - 8
8 ** 3
