"""
ClassDef astroid node

A class definition.

Attributes:
    - decorators  (Decorators)
        - The decorator to be applied on this function.
    - bases       (List[Node])
        - List of nodes for explicitly specified base classes.
    - body        (List[Node])
        - List of nodes representing the code within the class definition.

Example:
    - decorators  -> @wrapper
    - bases       -> [Name(id='base1', ctx=Load()),Name(id='base2', ctx=Load())]
    - body        -> [Pass()]
"""

@wrapper
class foo(base1, base2, metaclass=meta):
    pass
