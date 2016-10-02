"""
ExtSlice astroid node

Extended slicing which most python objects like list and string don't support.

Attributes:
    - dims  (Slice)
        - Holds a Slice node.

Example:
    - dims  -> Slice(lower=Num(n=2), upper=Num(n=3), step=None)
"""

class Foo(object):
    def __getitem__(self, item):
        return item

foo = Foo()
print(foo[1, 2:3])
# (1, slice(2, 3, None))
