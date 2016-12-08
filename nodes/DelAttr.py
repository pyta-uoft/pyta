"""
DelAttr astroid node

This node represents the part where an attribute of an object is being deleted.

Attributes:
    - expr      (Name)
        - The node object whose attribute is being deleted.
    - attrname  (str)
        - The name of the attribute being deleted.

Example:
    - expr      -> Name("self", Del())
    - attrname  -> "attr"
"""

class Foo():
    def __init__(self):
        self.attr = 1
        del self.attr
