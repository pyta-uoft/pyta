"""
Set astroid node

This node represents the Python set object.

Attributes:
    - elts  (List[Expr])
        - The elements in this set, which can be any immutable/hashable
          type expression.

Example 1:
    - elts  -> [Const(value=0)]

Example 2:
    - elts  -> [Const(value=1), Const(value=2), Const(value='hi')]


Type-checking:
    Type is Set[T], where T is the most specific class that every element
    of the list is an instance of.
"""

# Example 1
{0}

# Example 2
{1, 2, "hi"}
