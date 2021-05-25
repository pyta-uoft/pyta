"""
DictComp astroid node

A DictComp node represents dictionary comprehensions in Python.

Attributes:
    - key           (NodeNG)
        - The key that will be evaluated for each value.
    - value         (NodeNG)
        - The value that will be evaluated for each iteration.
    - generators    (list[Comprehension])
        - A list of comprehension node. See Comprehension node for more details.

Example 1:
    DictComp(
        key=Call(
            func=Name(name='str'),
            args=[Name(name='n')],
            keywords=None),
        value=Name(name='n'),
        generators=[Comprehension(
                is_async=0,
                target=AssignName(name='n'),
                iter=Call(
                    func=Name(name='range'),
                    args=[Const(value=3)],
                    keywords=None),
                ifs=[])])

Example 2:
    DictComp(
       key=Name(name='x'),
       value=Name(name='x'),
       generators=[Comprehension(
                 is_async=0,
                 target=AssignName(name='x'),
                 iter=Name(name='y'),
                 ifs=[])])

Example 3:
    DictComp(
       key=Name(name='z'),
       value=Name(name='y'),
       generators=[Comprehension(
             is_async=0,
             target=AssignName(name='z'),
             iter=Name(name='a'),
             ifs=[]),
          Comprehension(
             is_async=0,
             target=AssignName(name='y'),
             iter=Name(name='b'),
             ifs=[])])

Type-checking:
    The type of the DictComp is dict[K, V], where K is the type of key and V is the type of value.
"""

# Example 1
{str(n): n for n in range(3)}

# Example 2
{x: x for x in y}

# Example 3
{z: y for z in a for y in b}
