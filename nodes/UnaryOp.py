"""
UnaryOp astroid node

This node represents unary operators such as positive, negation, and
inversion (complementing).

See https://docs.python.org/3/reference/expressions.html#unary-arithmetic-and-bitwise-operations.

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

Type-checking:
    Translate the operator into the corresponding method, and type-check the method call.
"""

# Example 1:
not None

# Example 2:
+5

# Example 3:
-x

# Example 4:
~72
