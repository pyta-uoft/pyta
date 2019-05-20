"""
AugAssign astroid node

An augmented assignment, which is the combination, in a single statement, of a
binary operation and an assignment statement.

Attributes:
    - target  (Name | Subscript | Attribute)
        - A single node
    - value   (Node)
        - A single node to be assigned to target.
    - op      (str)
        - The operator to be performed on target.

Type-checking:
    See https://docs.python.org/3.6/reference/datamodel.html#emulating-numeric-types.
    Attempt to type-check the method call directly corresponding to 'op' (e.g.,
    '__iadd__' for '+='). Otherwise, fallback to the corresponding standard
    operator (e.g., '__add__' for '+='), making sure to auto-convert arguments
    if necessary (as in BinOp).


Example 1:
    - target  -> AssignName(name='x')
    - value   -> Const(value=1)
    - op      -> '+='
"""

# Example 1:
x += 1
