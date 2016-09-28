"""
DelAttr astroid node

DelAttr deletes the named attribute, provided the object allows it. For example,
delattr(x, 'foobar') is equivalent to del x.foobar.

Attributes:
    - object  (object)
        - The object which its attribute is being deleted.
    - name    (str)
        - The name of the attribute being deleted. The string must be the name
          of one of the attributes of object.

Example:
    - object  -> self
    - name    -> "attr"
"""

class Foo():
    def __init__(self):
        self.attr = 1
        del self.attr
