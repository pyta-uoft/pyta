"""
Index astroid node

This node represents simple subscripting with a single value.

Attributes:
    - value  (Expr)
        - The Expr node can be Const, UnaryOp, BinOp, etc.

Example 1:
    - value  -> Const(0)

Example 2:
    - value -> UnaryOp(-1)

Example 3:
    - value -> BinOp(1, 2)

Type-checking:
    Index nodes take the same type as their value.
"""

# Example 1:
x[0]

# Example 2:
x[-1]

# Example 3:
x[1+2]
