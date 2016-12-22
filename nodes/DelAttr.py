"""
DelAttr astroid node

This is an astroid Attribute node specifically in the Del (being deleted) context,
that is, the attribute of another node that is being deleted.

Attributes:
    - expr      (Node)
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
