"""
AugAssign astroid node

An augmented assignment, which is the combination, in a single statement, of a
binary operation and an assignment statement.

Attributes:
    - target  (List[Name | Subscript | Attribute])
        - A list of nodes. Multiple nodes represent assigning the same value.
          to each.
    - value   (Node)
        - A single node to be assigned to target.
    - op      (Expr)
        - The operator to be performed on target.

Example:
    - target  -> [Name(id='x', ctx=Store())]
    - value   -> Num(n=1)
    - op      -> Add()
"""

x += 1
