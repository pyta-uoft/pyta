"""
Decorators astroid node

A decorator is a function that alters the functionality of a function, method,
or class without having to directly use subclasses or change the source code of
the function being decorated. A Decorators node is a child node of FunctionDef
node.

Attributes:
    - nodes  (List[Name])
        - A list of names of the decorators

Example:
    - nodes  -> [Name(name='wrapper'), Name(name='decor')]
"""

@wrapper
@decor
def fun():
    pass
