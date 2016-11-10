"""
Decorators astroid node

A Decorator is a function that alters the functionality of a function, method,
or class without having to directly use subclasses or change the source code of
the function being decorated. In this case, wrapper turns from a FunctionDef
node to a Decorators node when it is assigned to decorate function fun().

Attributes:
    - nodes  (Decorators)
        - Represents a decorators node.

Example:
    - nodes  -> wrapper
"""

@wrapper
def fun():
    pass
