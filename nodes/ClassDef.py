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
    - decorators  -> @wrapper
    - bases       -> [Name(id='base1', ctx=Load()),Name(id='base2', ctx=Load())]
    - body        -> [Pass()]

Type-checking:
    The class name is added to the parent's type environment.
    The class' instance variables and methods are used to update the global TypeStore.
"""

@wrapper
class Foo(base1, base2):
    pass
