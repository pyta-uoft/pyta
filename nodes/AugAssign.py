"""
AugAssign astroid node

An augmented assignment, which is the combination, in a single statement, of a
binary operation and an assignment statement.

Attributes:
    - target  (Name | Subscript | Attribute)
        - A list of nodes. Multiple nodes represent assigning the same value.
          to each.
    - value   (Node)
        - A single node to be assigned to target.
    - op      (Expr)
        - The operator to be performed on target.

Example:
    - target  -> x
    - value   -> 1
    - op      -> +=
"""

x += 1
