"""
ExtSlice astroid node

Extended slicing which most python objects like list and string don't support.

Attributes:
    - dims  (List[Slice | Index])
        - Holds a Slice node.

Example:
    - dims  -> [Slice(lower=Const(value=2), upper=Const(value=3), step=None),
                Index(value=Const(value=1)]

Type-checking:
    The inferred type is a tuple consisting of the inferred types of the 'dims'.
"""

class Foo(object):
    def __getitem__(self, item):
        return item

foo = Foo()
print(foo[1, 2:3])
# (1, slice(2, 3, None))
