"""
UnaryOp astroid node

This node represents unary operators such as positive, negative, negation, and
inversion (complementing).

Attributes:
    - op       (class[UAdd | USub | Not | Invert])
        - The unary operation to be performed on the operand.
    - operand  (Expr | None)
        - The single expression to be operated on.

Example 1:
    - op       -> Not
    - operand  -> None

Example 2:
    - op       -> UAdd
    - operand  -> Num(5)

Example 3:
    - op       -> USub
    - operand  -> Name('x', Load())

Example 4:
    - op       -> Invert
    - operand  -> Num(72)
"""

# Example 1:
not None

# Example 2:
+5

# Example 3:
-x

# Example 4:
~72
