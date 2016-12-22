"""
Attribute astroid node

To give attribute access. (This is only for Attribute nodes appearing
in a Store context. For more information, see the README.)

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
