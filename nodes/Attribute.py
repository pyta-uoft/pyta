"""
Attribute astroid node

To give attribute access.

Attributes:
    - expr      (Node)
        - Those node object whose attribute is given access to.
    - attrname  (str)
        - The name of the access.

Example:
    - expr      -> Name(id='snake', ctx=Load())
    - attrname  -> "colour"
"""

snake.colour
