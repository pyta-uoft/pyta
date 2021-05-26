"""
AssignAttr astroid node

To assign a value to the relationship attribute. (This is the astroid
Attribute node in the specific Load context.)

Attributes:
    - attrname  (Optional[str])
        - The name of the attribute that is assigned.
    - expr      (Optional[NodeNG])
        - The node object whose attribute is assigned.

Example:
    AssignAttr(
        attrname='name',
        expr=Name(name='self'))
"""

class ClassName():
    def __init__(self, name):
        self.name = name
