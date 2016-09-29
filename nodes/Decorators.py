"""
Decorators astroid node

A Decorator is a function that alters the functionality of a function, method,
or class without having to directly use subclasses or change the source code of
the function being decorated. In this case, wrapper is a pre-written decorator
function and fun is the function being decorated.

Attributes:
    - decorator_list  (List[Decorators])
        - The list of decorators to be applied. See FunctionDef.py for an
          example.
    - name            (str)
        - The name of the decorator function with type str.
    - args            (Node[Arguments])
        - The argument of decorator is a function, method, or class.
    - body            (list)
        - The list of nodes inside the decorator function.
    - returns         (None)
        - The return annotation.

Example:
    - decorator_list  -> []
    - name            -> "wrapper"
    - args            -> fun()
    - body            -> None
"""

@wrapper
def fun():
    pass
