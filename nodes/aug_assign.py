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

Type-checking:
    See https://docs.python.org/3.6/reference/datamodel.html#emulating-numeric-types.
    Attempt to type-check the method call directly corresponding to 'op' (e.g.,
    '__iadd__' for '+='). Otherwise, fallback to the corresponding standard
    operator (e.g., '__add__' for '+='), making sure to auto-convert arguments
    if necessary (as in BinOp).


Example:
    AugAssign(
        op='+=',
        target=AssignName(name='x'),
        value=Const(value=1))
"""

# Example:
x += 1
