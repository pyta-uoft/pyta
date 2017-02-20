"""
Set astroid node

This node represents the Python set object.

Attributes:
    - elts  (List[Expr])
        - The elements in this set, which can be any immutable/hashable
          type expression.

Example 1:
    - elts  -> []

Example 2:
    - elts  -> [Const(int(1)), Const(int(2)), Const(str(hi))]
"""

# Example 1
{0}

# Example 2
{1, 2, "hi"}
