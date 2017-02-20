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
"""

1 + 2
