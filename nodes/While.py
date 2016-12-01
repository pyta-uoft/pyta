"""
While astroid node

This node represents the Python while loop structure.

Attributes:
    - test    (Expr)
        - The boolean-valued expression to determine whether the loop continues.
    - body    (List[Statement])
        - The code to be performed while the loop condition is true.
    - orelse  (List[Statement])
        - The code in the else statement (to be performed once the loop exits).

Example:
    - test    -> Const(True)
    - body    -> [Node(Break)]
    - orelse  -> [Node(Pass)]
"""

while True:
    break
else:
    pass
