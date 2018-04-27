"""
BoolOp astroid node

A boolean operation, 'or' or 'and'.

Attributes:
    - values  (Expr)
        - The values involved.
    - op      (Or | And)
        - The operator, Or or And.

Example:
    - values  -> None, 1
    - op      -> Or

Type-checking:
    If all of the values have the type type, that type is used as the type of the of BoolOp itself.
    Otherwise, the type of the BoolOp is Any.
"""

x = None or 1
