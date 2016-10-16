"""
Global astroid node

Global sets a variable to be a global variable which can be called outside of
the scope of a function.

Attributes:
    - names  (List[str])
        - Names of variables whose values are to be assigned to the
          corresponding global variable.

Example:
    - names  -> ['x', 'y']
"""

def fun():
    global x, y
