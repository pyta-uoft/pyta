"""
Set astroid node

This node represents the Python set object.

Attributes:
    - elts  (list[Expr])
        - The elements in this set, which can be any immutable/hashable
          type expression.

Example 1:
    Set(elts=[Const(value=0)])

Example 2:
    Set(elts=[
        Const(value=1),
        Const(value=2),
        Const(value='hi')]
"""

# Example 1
{0}

# Example 2
{1, 2, "hi"}
