"""
For astroid node

Represents a for loop.

Attributes:
    - target  (Node)
        - Holds the variable(s) the loop assigns to as a single node. The type
          of the node can be Name, List, Tuple, etc.
    - iter    (Node)
        - A List node representing the iterable.
        - Can also be a Call node (ie. representing a range function call).
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
"""

for i in [1, 2, 3]:
    break
else:
    pass

# TODO: Add example of for-else loop iterating over generator returned by range
# call."

