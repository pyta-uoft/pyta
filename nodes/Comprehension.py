"""
Comprehension astroid node

Constructs that allow sequences to be built from other sequences.

Attributes:
    - target  (Node)
        - Typically a name or tuple node; the reference to use for each element.
    - iter    (Node)
        - The object to iterate over.
    - ifs     (List[Expr])
        - List of test expressions.

Example:
    - target  -> x
    - iter    -> range(3)
    - ifs     -> []
"""

[x for x in range(3)]
