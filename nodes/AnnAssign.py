"""
AnnAssign astroid node

A node representing an annotated assignment statement.

Attributes:
    - annotation         (Node)
        - A Name node representing the type of the variable.
    - target        (Node)
        - An AssignName node representing the name of the variable being
        assigned to.

Example:
    - annotation   -> Name.str(name='str')
    - target       -> AssignName.name(name='name')
"""

class Student:
    name: str
    age: int
    status: bool
    def __init__(self):
        pass

