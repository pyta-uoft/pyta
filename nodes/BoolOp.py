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
    - op      -> or
"""

x = None or 1
