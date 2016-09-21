"""
Keyword astroid node

A keyword argument, kwargs, to a function call or class definition.

Attributes:
    - arg    (str)
        - A string of the parameter name.
    - value  (Node)
        - A node to pass in to arg.

Example:
    - arg    -> "object"
    - value  -> Num(2)
"""

str(object=2)
