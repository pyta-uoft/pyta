"""
AssignAttr astroid node

To assign a value to the relationship attribute.

Attributes:
    - expr      (Expr)
        - An expression to be assigned.
    - attrname  (Node)
        - The name that is assigned to the expression.

Example:
    - expr      -> 'name'
    - attrname  -> 'self.name'
"""

class ClassName():
    def __init__(self, name):
        self.name = name
