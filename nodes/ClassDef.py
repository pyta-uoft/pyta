"""
ClassDef astroid node

A class definition.

Attributes:
    - decorators  (List[Node])
        - List of nodes.
    - bases       (List[Node)
        - List of nodes for explicitly specified base classes.
    - body        (List[Node])
        - List of nodes representing the code within the class definition.

Example:
    - decorators  -> @wrapper
    - bases       -> Classname()
    - body        -> [pass]
"""

@wrapper
class ClassName():
    pass
