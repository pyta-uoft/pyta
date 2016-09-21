"""
Decorators astroid node

Attributes:
    - decorator_list  (list)  the list of decorators to be applied
    - name            (str)   the string of the function name
    - body            (list)  the list of nodes inside the function

Example:
    - decorator_list  -> [@wrapper]
    - name            -> "fun"
    - body            -> [pass]
"""

@wrapper
def fun():
    pass
