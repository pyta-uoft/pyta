"""
Set astroid node

This node represents the Python set object.

Attributes:
    - elts  (List[Expr])
        - The elements in this list, which can be any immutable/hashable
          type expression.

Example 1:
    - elts  -> []

Example 2:
    - elts  -> [Num(1), Num(2), Str(hi)]
"""

# Example 1
{0}

# Example 2
{1, 2, "hi"}
