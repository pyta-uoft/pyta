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
    - elts  -> [Const(value=1), Const(value=2), Const(value=3)]
    - ctx   -> Load

Example 3:
    - elts  -> [AssignName(name='x'), AssignName(name='y')]
    - ctx   -> Store


Type-checking:
    Type is List[T], where T is the most specific class that every element
    of the list is an instance of.
"""

# Example 1
[]

# Example 2
[1, 2, 3]

# Example 3
[x, y] = 7, 8
