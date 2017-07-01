"""
IfExp astroid node

An if statement written in an expression form.
(IfExp node represents an expression, not a statement.)

Attributes:
    - test    (Node)
        - Holds a single node such as Compare.
    - body    (Node)
        - A Node representing the suite to be executed if the if expression
          evalutes to True.
    - orelse  (Node)
        - The Node representing the suite to be executed if the if expression
          evaluates to False.

Example:
    - test    -> Const(True)
    - body    -> Const(1)
    - orelse  -> Const(0)
"""

x = 1 if True else 0

