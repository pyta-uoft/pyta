"""
AugAssign astroid node

An augmented assignment, which is the combination, in a single statement, of a
binary operation and an assignment statement.

Attributes:
    - target  (Node(Name|Subscript|Attribute))
        - A list of nodes. Multiple nodes represents assigning the same value.
          to each.
    - op      (Node(Add))
        - The operator to be performed on target.
    - value   (Node(Num))
        - A single node to be assigned to target.

Example:
    - target  -> x
    - op      -> +=
    - value   -> 1
"""

x += 1
