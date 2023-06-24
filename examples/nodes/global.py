"""
Global astroid node

Global sets a variable to be a global variable which can be called outside of
the scope of a function.

Attributes:
    - names (list[str])
        - Names of variables whose values are to be assigned to the
          corresponding global variable.

Example 1:
    Global(names=['x'])

Example 2:
    Global(names=['x', 'y'])
"""

# Example 1
global x

# Example 2
global x, y
