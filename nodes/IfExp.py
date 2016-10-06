"""
IfExp astroid node

An if statement written in an expression form.

Attributes:
    - test    (Node)
        - Holds a single node such as Compare.
    - Body    (List[Node])
        - A list of nodes that will execute if the condition passes.
    - orelse  (List[Node])
        - The else clause.

Example:
    - test    -> True
    - Body    -> [x = 1]
    - orelse  -> [0]
"""

x = 1 if True else 0
