"""
GeneratorExp astroid node

A generator expressions is a high performance, memory efficient generalization
of list comprehensions. It is used when iterating over the elements one at a
time.

Attributes:
    - elt         (Node)
        - Represents the part that will be evaluated for each item.
    - generators  (List[Node])
        - Nodes are comprehension nodes. See Comprehension.py for more details.

Example:
    - elt         -> g
    - generators  -> [comprehension(for ip in num),
                     comprehension(for num in range(9)))]
"""

(g for ip in num for num in range(9))
