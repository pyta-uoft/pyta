"""
Keyword astroid node

A keyword argument, kwargs, to a function call or class definition.

Attributes:
    - arg: str
        - A string of the parameter name.
    - value: NodeNG
        - A node to pass into the arg.

Example 1:
    Keyword(
       arg='object',
       value=Const(value=2))
"""

str(object=2)
