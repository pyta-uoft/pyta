"""
For astroid node

A for loop.

Attributes:
    - target  (Node(Name|Tuple|List))
        - Holds the variable(s) the loop assigns to as a single node.
    - iter    (Node)
        - Holds the item to be looped over.
    - body    (List[Node])
        - Contains lists of nodes to execute.
    - orelse  (List[Node])
        - Nodes will execute if the loop finished normally rather than via a
        break statement.

Example:
    - target  -> i
    - iter    -> i in range(3)
    - body    -> [break]
    - orelse  -> None
"""

for i in range(3):
    break
