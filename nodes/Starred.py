"""
Starred astroid node

This node represents a starred variable reference, used for unpacking iterables
into lists. This type of node usually appears under a List, Tuple, or Call node.

Attributes:
    - value  (Name)
        - The variable to be unpacked into as a list.
    - ctx    (class[expr_context])
        - The context in which this starred variable is used, one of
          Load or Store.

Example 1: (nested in Tuple node)
    - value  -> Name('a', Store())
    - ctx    -> Store

Example 2: (nested in Call node)
    - value  -> Name('x', Load())
    - ctx    -> Load
"""

# Example 1
*a, b = range(5)

# Example 2
print(*x)
