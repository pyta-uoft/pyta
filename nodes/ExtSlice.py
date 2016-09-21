"""
ExtSlice astroid node

Attributes:
    - dims  (list)  holds a list of Slice and Index nodes

Example:
    - dims  -> [Slice(lower=Num(n=2), upper=Num(n=3), step=None),
               Index(value=Num(n=1))
"""

class Foo(object):
    def __getitem__(self, item):
        return item

foo = Foo()
print(foo[1, 2:3])  # (1, slice(2, 3, None))
