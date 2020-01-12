"""
Attribute astroid node

An expression accessing an object's attribute (This is only for Attribute nodes appearing
in a Load context. For more information, see the README.)

Attributes:
    - expr (Node)
        - The node object whose attribute is given access to.
    - attrname  (str)
        - The name of the accessed attribute.

Example:
    - expr      -> Name(name='snake')
    - attrname  -> "colour"

Type-checking:
    The type of `expr` is resolved, and attrname is looked up for that type.
    (Currently in TypeStore only, for built-in types.)
"""

snake.colour
