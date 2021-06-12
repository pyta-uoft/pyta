"""
While astroid node

This node represents the Python while loop structure.

Attributes:
    - test    (Expr)
        - The boolean-valued expression to determine whether the loop continues.
    - body    (list[Statement])
        - The code to be performed while the loop condition is true.
    - orelse  (list[Statement])
        - The code in the else statement (to be performed once the loop exits).

Example:
    While(
        test=Const(value=True),
        body=[Break()],
        orelse=[Pass()])
"""

while True:
    break
else:
    pass
