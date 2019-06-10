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
    - op       -> 'not'
    - operand  -> Const(value=None)

Example 2:
    - op       -> '+'
    - operand  -> Const(value=5)

Example 3:
    - op       -> '-'
    - operand  -> Name(name='x')

Example 4:
    - op       -> '~'
    - operand  -> Const(value=72)

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
