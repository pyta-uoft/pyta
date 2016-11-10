"""
Slice astroid node

This node represents the Python slicing operator, used to isolate parts of
an iterable. It is used in the Subscript node.

Attributes:
    - lower  (Num)
        - The optional lower bound of this slice, an integer. 0 by default.
    - upper  (Num)
        - The optional upper bound (non-inclusive) of this slice, an integer.
          The length of the iterable being sliced by default.
    - step   (Num)
        - The optional step (number of iterations to skip) for this slice,
          an integer. None by default.

Example 1:
    - lower  -> 0
    - upper  -> 2
    - step   -> None

Example 2:
    - lower  -> 1
    - upper  -> 2
    - step   -> None

Example 3:
    - lower  -> 1
    - upper  -> -1
    - step   -> 3
"""

a = ['p', 'y']

# Example 1
a[:]

# Example 2
a[1:]

# Example 3
a[1:-1:3]
