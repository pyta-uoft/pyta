"""
ListComp astroid node

This node represents list comprehension expressions in Python, which take the
form [element for increment in iterable]. This node also makes use of the
Comprehension node.

Attributes:
    - elt         (Expr)
        - The part to be evaluated to make every item in the list. This can
          be any expression node, such as a BinOp or Str.
    - generators  (List[Comprehension])
        - This list contains one Comprehension node for every "for" clause
          in this list comprehension.

Example 1:
    - elt         -> l+l
    - generators  -> [Comprehension(l, "str", [])]

Example 2:
    - elt         -> x*y
    - generators  -> [Comprehension(x, [1, 2, 3], []),
                      Comprehension(y, [4, 5, 6], [])]

Type-checking:
    The type of the ListComp is List[T], where T is the type of elt.
"""

# Example 1
[l+l for l in "str"]

# Example 2
[x*y for x in [1, 2, 3] for y in [4, 5, 6]]
