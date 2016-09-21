"""
DelAttr astroid node

Attributes:
    - targets  (list)  the targets to be deleted of type Attributes

Example:
    - targets  -> self.attr
"""

class Foo():
    def __init__(self):
        self.attr = 1
        del self.attr
