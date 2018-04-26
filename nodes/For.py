"""
For astroid node

Represents a for loop.

Attributes:
    - target  (Node)
        - Holds the variable(s) the loop assigns to as a single node. The type
          of the node can be Name, List, Tuple, etc.
    - iter    (Node)
        - A node which represents the iterable.
          the loop.
    - body    (List[Statement])
        - The node to be executed.
    - orelse  (List[Statement])
        - The nodes will execute if the loop finished normally rather than via a
        break statement.

Example:
    - target  -> AssignName(i)
    - iter    -> List(Const.int(Value=1), Const.int(Value=2),
    Const.int(Value=3)))
    - body    -> [Break()]
    - orelse  -> [Pass()]

Type-checking:
    Unify the target against the "contained" type in the iterable.
"""

for i in [1, 2, 3]:
    break
else:
    pass

for i in range(3):
    break
else:
    pass

