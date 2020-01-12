"""
SetComp astroid node

This node represents set comprehension expressions in Python, which take the
form {element for increment in iterable}. This node also makes use of the
Comprehension node.

Attributes:
    - elt         (Expr)
        - The part to be evaluated to make every item in the set. This can
          be any expression node, such as a BinOp or Str.
    - generators  (List[Comprehension])
        - This list contains one Comprehension node for every "for" clause
          in this set comprehension.

Example 1:
    - elt         -> x * 2
    - generators  -> [Comprehension(x, [1], [])]

Example 2:
    - elt         -> x * y
    - generators  -> [Comprehension(x, [0, 1, 2], []),
                      Comprehension(y, [4, 3, 2], [Compare(x < y)])]

Type-checking:
    The type of the SetComp is Set[T], where T is the type of elt.
"""

# Example 1
{x * 2 for x in [1]}

# Example 2
{x * y for x in [0, 1, 2] for y in [4, 3, 2] if x < y}
