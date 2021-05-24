"""
Nonlocal astroid node

This node represents statements formed with the Python "nonlocal" identifier,
which causes the identified variable names to be interpreted as referring to
the variables with those names previously bound in the nearest enclosing
(non-global) scope. Note that several variables can be rebound in the same
Nonlocal statement. Also, variables already defined in the current scope trying
be rebound as nonlocals will raise a SyntaxWarning.

Attributes:
    - names  (list[str])
        - The raw names of variables to be rebound as nonlocal.

Example:
    Nonlocal(names=['x', 'y'])
"""

def outer():
    x = y = 1
    def inner():
        nonlocal x, y
        x += y
    inner()
