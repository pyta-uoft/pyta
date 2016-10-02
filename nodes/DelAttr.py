"""
DelAttr astroid node

DelAttr deletes the named attribute, provided the object allows it. For example,
delattr(x, 'foobar') is equivalent to del x.foobar.

Attributes:
    - expr      (Node)
        - The node object whose attribute is being deleted.
    - attrname  (str)
        - The name of the attribute being deleted.

Example:
    - expr      -> Foo
    - attrname  -> "attr"
"""

class Foo():
    def __init__(self):
        self.attr = 1
        del self.attr
