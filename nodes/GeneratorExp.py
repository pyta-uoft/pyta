"""
GeneratorExp astroid node

A generator expressions is a generator object that is used when iterating over
the elements one at a time.

Attributes:
    - elt         (Node)
        - Represents the node that will be evaluated for each item.
    - generators  (List[Comprehension])
        - Nodes are comprehension nodes. See Comprehension.py for more details.
    - locals      (Dict)
        - The variables in the local scope.

Example:
    - elt         -> g
    - generators  -> [comprehension(ip, num),
                     comprehension(num, range(9)))]
    - locals      -> {'elt': g, 'generators': [comprehension(ip, num),
                     comprehension(num, range(9)))]}
"""

(g for ip in num for num in range(9))
