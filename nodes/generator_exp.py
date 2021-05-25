"""
GeneratorExp astroid node

A generator expressions is a generator object that is used when iterating over
the elements one at a time.

Attributes:
    - elt           (NodeNG)
        - Represents the node that will be evaluated for each item.
    - generators    (list[Comprehension])
        - Nodes are comprehension nodes. See Comprehension.py for more details.

Example:
    GeneratorExp(
        elt=Tuple(
            ctx=<Context.Load: 1>,
            elts=[Name(name='i'), Name(name='j')]),
        generators=[Comprehension(
            is_async=0,
            target=AssignName(name='i'),
            iter=Call(
                func=Name(name='range'),
                args=[Const(value=4)],
                keywords=None),
            ifs=[]),
        Comprehension(
            is_async=0,
            target=AssignName(name='j'),
            iter=Call(
                func=Name(name='range'),
                args=[Name(name='i')],
                keywords=None),
            ifs=[])])

Type-checking:
    The type of the GeneratorExp is Generator[T, None, None], where T is the type of elt.
"""

# Example
((i, j) for i in range(4) for j in range(i))
