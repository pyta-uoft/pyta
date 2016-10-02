"""
For astroid node

A for loop.

Attributes:
    - target  (Node(Name|Tuple|List))
        - Holds the variable(s) the loop assigns to as a single node.
    - iter    (Node)
        - The node to be looped over.
    - body    (Node)
        - The node to be executed.
    - orelse  (Node)
        - Node will execute if the loop finished normally rather than via a
        break statement.

Example:
    - target  -> i
    - iter    -> i in range(3)
    - body    -> break
    - orelse  -> None
"""

for i in range(3):
    break
