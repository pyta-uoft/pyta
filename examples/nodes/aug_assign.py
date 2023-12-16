"""
AugAssign astroid node

An augmented assignment, which is the combination, in a single statement, of a
binary operation and an assignment statement.

Attributes:
    - op      (Optional[str])
        - The operator to be performed on target.
    - target  (Optional[Name | Subscript | Attribute])
        - What is being assigned to.
    - value   (Optional[NodeNG])
        - A single node to be assigned to target.

Example:
    AugAssign(
        op='+=',
        target=AssignName(name='x'),
        value=Const(value=1))
"""

# Example:
x += 1
