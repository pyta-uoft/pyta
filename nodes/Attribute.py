"""
Attribute astroid node

To give attribute access.

Attributes:
    - expr      (Node)
        - Those node object whose attribute is given access to.
    - attrname  (str)
        - The name of the access.

Example:
    - expr      -> ''
    - attrname  -> 'endswith', ctx=Load()
"""

''.endswith('')
