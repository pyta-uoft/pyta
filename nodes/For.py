"""
For astroid node

Represents a for loop.

Attributes:
    - target  (Node)
        - Holds the variable(s) the loop assigns to as a single node. The type
          of the node can be Name, List, Tuple, etc.
    - iter    (Call)
        - A function call node which represents the part that iterates over
          the loop.
    - body    (List[Statement])
        - The node to be executed.
    - orelse  (List[Statement])
        - The nodes will execute if the loop finished normally rather than via a
        break statement.

Example:
    - target  -> AssignName(i)
    - iter    -> Call(func = Name(range), args = [3])
    - body    -> [Break()]
    - orelse  -> [Pass()]
"""

for i in range(3):
    break
else:
    pass
