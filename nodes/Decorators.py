"""
Decorators astroid node

A decorator is a function that alters the functionality of a function, method,
or class without having to directly use subclasses or change the source code of
the function being decorated. A Decorators node is a child node of FunctionDef
node.

Attributes:
    - nodes  (Node)
        - Represents a decorators node.

Example:
    - nodes  -> wrapper
"""

@wrapper
def fun():
    pass
