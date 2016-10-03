"""
List astroid node

This node represents the Python list objects.

Attributes:
    - elts  (List[Expr])
        - The elements in this list, which can be any expression.
    - ctx   (class[expr_context])
        - The context in which this list is to be used, either Load or Store.

Example 1:
    - elts  -> []
    - ctx   -> Load

Example 2:
    - elts  -> [Num(1), Num(2), Num(3)]
    - ctx   -> Load

Example 3:
    - elts  -> [Num(1), Num(2)]
    - ctx   -> Store
"""

# Example 1
[]

# Example 2
[1, 2, 3]

# Example 3
[x, y] = 7, 8
