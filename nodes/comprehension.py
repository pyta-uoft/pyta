"""
Comprehension astroid node

Constructs that allow sequences to be built from other sequences.

Attributes:
    - ifs               (List[NodeNG])
        - List of test expressions. If None, ifs is an empty list.
    - is_async          (bool)
        - Whether this is an asynchronous comprehension or not.
    - iter              (NodeNG)
        - The object to iterate over.
    - optional_assign   (bool)
        - Whether this node optionally assigns a variable
    - target            (NodeNG)
        - Typically a name or tuple node; the reference to use for each element.

Example 1:
    * NOTE : The example below is of a Comprehension Node "for x in range(3)" within
             a ListComprehension Node "[x for x in range(3)]".

    - Comprehension(
                     is_async=0,    # This was the return of repr_tree.__str__() as an int
                     target=AssignName(name='x'),
                     iter=Call(
                        func=Name(name='range'),
                        args=[Const(value=3)],
                        keywords=None),
                     ifs=[])

Example 2:
    * NOTE : The example below is of a Comprehension Node "b in range(3) if b < 2" within
             a ListComprehension Node "[b for b in range(3) if b < 2]".

    - Comprehension(
                     is_async=0,
                     target=AssignName(name='b'),
                     iter=Call(
                        func=Name(name='range'),
                        args=[Const(value=3)],
                        keywords=None),
                     ifs=[Compare(
                           left=Name(name='b'),
                           ops=[['<', Const(value=2)]])])

Type-checking:
    Unify the target against the "contained" type in the iterable.
"""

# Example 1
[x for x in range(3)]

# Example 2
[b for b in range(3) if b < 2]

