"""
DelAttr astroid node

This node represents an attribute of an object being deleted.
This is an astroid Attribute node specifically in the Del (being deleted) context.

Attributes:
    - expr      (Name)
        - The node object whose attribute is being deleted.
    - attrname  (str)
        - The name of the attribute being deleted.

Example:
    - expr      -> Name(id="self")
    - attrname  -> "attr"
"""

class Foo():
    def __init__(self):
        self.attr = 1
        del self.attr
