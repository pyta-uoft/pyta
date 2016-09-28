"""
Expr astroid node

When an expression, such as a function call, appears as a statement by itself
with its return value not used or stored, it is wrapped in Expr node.

Attributes:
    - value  (node)
        - Value holds a Name, a Lambda, or a Yield or YieldFrom node.

Example:
    - value  -> print(1)
"""

print(1)
