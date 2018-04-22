"""
Attribute astroid node

To give attribute access. (This is only for Attribute nodes appearing
in a Load context. For more information, see the README.)

Attributes:
    - expr      (Node)
        - Those node object whose attribute is given access to.
    - attrname  (str)
        - The name of the access.

Example:
    - expr      -> Name(id='snake', ctx=Load())
    - attrname  -> "colour"

Type-checking:
    The type of `expr` is resolved, and attrname is looked up for that type.
    (Currently in TypeStore only, for built-in types.)
"""

snake.colour
