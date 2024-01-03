"""
Attribute astroid node

An expression accessing an object's attribute (This is only for Attribute nodes appearing
in a Load context. For more information, see the README.)

Attributes:
    - attrname  (Optional[str])
        - The name of the accessed attribute.
    - expr (Optional[Name])
        - The Name object whose attribute is given access to.

Example:
    Attribute(
        attrname='colour',
        expr=Name(name='snake'))
"""

snake.colour
