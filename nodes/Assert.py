"""
Assert astroid node

An assertion.

Attributes:
    - test  (Expr)
        - This holds the condition, such as a Compare node, to be evaluated
          True or False
    - fail  (Node)
        - Usually a str; the message shown if condition is False.

Example:
    - test  -> x == 0
    - fail  -> 'x isn't 0!' # AssertionError and this message if condition is
               False
"""

assert x == 0, "x isn't 0!"
