"""
Keyword astroid node

A keyword argument, kwargs, to a function call or class definition.

Attributes:
    - arg       (str)
        - A string of the parameter name.
    - value     (NodeNG)
        - A node to pass into the arg.

Example 1:
    Call(
        func=Name(name='str'),
        args=[],
        keywords=[Keyword(
                arg='object',
                value=Const(value=2))])

* Note that the Keyword is inside of the keywords list in the Call node.
"""

str(object=2)
