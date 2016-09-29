"""
If astroid node

An if statement.

Attributes:
    - test    (Node)
        - Holds a single node such as Compare.
    - Body    (List[Node])
        - A list of nodes that will execute if the condition passes.
    - orelse  (List[Node])
        - The else clause.

Example:
    - test    -> n > 2
    - Body    -> [pass]
    - orelse  -> [n = 3]
"""

if n > 2:
    pass
else:
    n = 3

