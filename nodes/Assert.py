"""
Assert astroid node

An assertion.

Attributes:
    - test  (Expr)
        - This holds the condition, such as a Compare node, to be evaluated
          True or False
    - fail  (Node | None)
        - Usually a str; the message shown if condition is False. If None, only
          AssertionError is shown.

Example:
    - test  -> Compare(left=Name(name='x'), ops=[['==', Const(value=0)]])
    - fail  -> Const("x isn't 0!") # AssertionError and this message if condition is
               False
"""

assert x == 0, "x isn't 0!"
