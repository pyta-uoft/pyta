"""
List astroid node

This node represents the Python list objects.

Attributes:
    - elts  (List[Assign_target])
        - The elements in this list, which can be any Assignment target
          type (Attribute, Subscript, Starred, Name, List, or Tuple).
    - ctx   (class[expr_context])
        - The context in which this list is to be used, either Load or Store.

Example 1:
    - elts  -> []
    - ctx   -> Load

Example 2:
    - elts  -> [Num(1), Num(2), Num(3)]
    - ctx   -> Load
"""

# Example 1
[]

# Example 2
[1, 2, 3]
