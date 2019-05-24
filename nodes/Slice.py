"""
Slice astroid node

This node represents the Python slicing operator, used to isolate parts of
an iterable. It is used in the Subscript node.

Attributes:
    - lower  (Expr)
        - The optional lower bound of this slice, which must evaluate to an
          integer. Default: 0.
    - upper  (Expr)
        - The optional upper bound (non-inclusive) of this slice, which must
          evaluate to an integer. Default: length of the iterable being sliced.
    - step   (Expr | None)
        - The optional step (number of iterations to skip) for this slice,
          which must evaluate to an integer. Default: None.

Example 1:
    - lower  -> None
    - upper  -> None
    - step   -> None

Example 2:
    - lower  -> Const(value=1)
    - upper  -> None
    - step   -> None

Example 3:
    - lower  -> 1
    - upper  -> -1
    - step   -> 3

Type-checking:
    Delegate to the __init__ constructor for slice, setting type to 'slice' on success.
"""

a = ['p', 'y']

# Example 1
a[:]

# Example 2
a[1:]

# Example 3
a[1:-1:3]
