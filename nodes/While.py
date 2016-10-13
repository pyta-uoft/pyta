"""
While astroid node

This node represents the Python while loop structure.

Attributes:
    - test    (Compare | Name)
        - The boolean loop condition to determine whether the loop continues.
    - body    (List[Stmt])
        - The code to be performed while the loop condition is true.
    - orelse  (List[Stmt])
        - The code in the else statement (to be performed once the loop exits).

Example:
    - test    -> Name(True)
    - body    -> [Node(Break)]
    - orelse  -> [Node(Pass)]
"""

while True:
    break
else:
    pass
