"""
For astroid node

Represents a for loop.

Attributes:
    - target    (NodeNG)
        - Holds the variable(s) the loop assigns to as a single node. The type
          of the node can be Name, List, Tuple, etc.
    - iter      (NodeNG)
        - A node which represents the iterable the loop iterates over.
    - body      (list[NodeNG])
        - The nodes to be executed per iteration of the loop
    - orelse    (list[NodeNG])
        - The nodes will execute if the loop finished normally rather than via a
        break statement.

Example 1:
    For(
        target=AssignName(name='i'),
        iter=Call(
            func=Name(name='range'),
            args=[Const(value=3)],
            keywords=None),
        body=[Break()],
        orelse=[])

Example 2:
    For(
        target=AssignName(name='i'),
        iter=List(
            ctx=<Context.Load: 1>,
            elts=[
                Const(value=1),
                Const(value=2),
                Const(value=3)]),
        body=[Break()],
        orelse=[Pass()])

Example 3:
    For(
        target=AssignName(name='_'),
        iter=Name(name='some_iterable'),
        body=[Break()],
        orelse=[])


Type-checking:
    Unify the target against the "contained" type in the iterable.
"""

# Example 1
for i in range(3):
    break

# Example 2
for i in [1, 2, 3]:
    break
else:
    pass

# Example 3
for _ in some_iterable:
    break
