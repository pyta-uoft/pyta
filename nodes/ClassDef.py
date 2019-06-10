"""
ClassDef astroid node

A class definition.

Attributes:
    - name        (str)
        - A raw string for the class name.
    - doc         (str)
        - The docstring of this function.
    - decorators  (Decorators)
        - The decorator to be applied on this function.
    - bases       (List[Node])
        - List of nodes for explicitly specified base classes.
    - body        (List[Node])
        - List of nodes representing the code within the class definition.

Example:
    - name        -> 'Foo'
    - doc         -> ''
    - decorators  -> Decorator(@wrapper)
    - bases       -> [Name(name='base1'),Name(name='base2')]
    - body        -> [Pass()]

Type-checking:
    The class name is added to the parent's type environment.
    The class' instance variables and methods are used to update the global TypeStore.
"""

@wrapper
class Foo(base1, base2):
    pass
