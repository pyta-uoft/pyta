"""
Nonlocal astroid node

This node represents statements formed with the Python "nonlocal" identifier,
which causes the identified variable names to be interpreted as referring to
the variables with those names previously bound in the nearest enclosing scope.
Note that several variables can be rebound in the same Nonlocal statement.

Attributes:
    - names  (List[str])
        - The raw names of variables to be rebound as nonlocal.

Example:
    - names  -> ['x', 'y']
"""

x = y = 1
def inner():
    nonlocal x, y
