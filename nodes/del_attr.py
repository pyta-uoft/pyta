"""
DelAttr astroid node

This node represents an attribute of an object being deleted.
This is an astroid Attribute node specifically in the Del (being deleted) context.

Attributes:
    - attrname  (Optional[str])
        - The name of the attribute being deleted.
    - expr      (Optional[Name])
        - The node object whose attribute is being deleted.

Example:
    DelAttr(
        attrname='attr',
        expr=Name(name='self'))
"""


class Foo:
    def __init__(self):
        self.attr = 1
        del self.attr
