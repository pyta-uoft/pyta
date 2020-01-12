"""
Comprehension astroid node

Constructs that allow sequences to be built from other sequences.

Attributes:
    - target  (Node)
        - Typically a name or tuple node; the reference to use for each element.
    - iter    (Node)
        - The object to iterate over.
    - ifs     (List[Expr])
        - List of test expressions. If None, ifs is an empty list.

Example 1:
    * NOTE : The example below is of a Comprehension Node "for x in range(3)" within
             a ListComprehension Node "[x for x in range(3)]".

    - target  -> AssignName(name='x')
    - iter    -> Call(func=Name(name='range'), args=[Const(value=3)])
    - ifs     -> []

Example 2:
    * NOTE : The example below is of a Comprehension Node "b in range(3) if b < 2" within
             a ListComprehension Node "[b for b in range(3) if b < 2]".

    - target  -> AssignName(name='b')
    - iter    -> Call(func=Name(name='range'), args=[Const(value=3)])
    - ifs     -> [Compare(left=Name(name='b'), ops=[['<', Const(value=2)]])]

Type-checking:
    Unify the target against the "contained" type in the iterable.
"""

# Example 1
[x for x in range(3)]

# Example 2
[b for b in range(3) if b < 2]

