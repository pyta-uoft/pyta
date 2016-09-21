"""
Dict astroid node

This is the node that represents the Python dictionary data type. It stores
the keys and values of a dict as parallel lists of equal length.

Attributes:
    - keys    (List[Expr])
        - The keys of this dict, which must be immutable/hashable type nodes
          (such as numbers, strings, and tuples).
    - values  (List[Expr])
        - The values of this dict, in the same order as the keys. These can
          be any expression node.

Example 1:
    - keys    -> ['b']
    - values  -> [1]

Example 2:
    - keys    -> [5, "hello"]
    - values  -> [[1, "cat" (6, 7, 8)], "goodbye"]
"""

# Example 1
a = {'b': 1}

# Example 2
b = {5: [1, "cat", (6, 7, 8)], "hello": "goodbye"}
