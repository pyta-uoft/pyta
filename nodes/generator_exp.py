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
    - elt         -> Name(name='j')
    - generators  -> [Comprehension(i, range(4)), Comprehension(j, range(9)))]
    - locals      -> {'i': [AssignName(name='i')], 'j': [AssignName(name='j')]}

Type-checking:
    The type of the GeneratorExp is Generator[T, None, None], where T is the type of elt.
"""

(j for i in range(4) for j in range(i))
