"""
AssignAttr astroid node

To assign a value to the relationship attribute.

Attributes:
    - expr      (Node)
        - The node object whose attribute is assigned.
    - attrname  (str)
        - The name of the attribute that is assigned.

Example:
    - expr      -> ClassName
    - attrname  -> "name"
"""

class ClassName():
    def __init__(self, name):
        self.name = name
