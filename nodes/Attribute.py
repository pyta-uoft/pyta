"""
Attribute astroid node

To give attribute access.

Attributes:
    - value  (Name|Other)
        - Typically a Name node.
    - attr   (Str)
        - Bare string that gives the name of the attribute
    - ctx    (class[expr_context])
        - The context in which this variable is used, one of Load, Store or Del.

Example:
    - value  -> ''
    - attr   -> ''
    - ctx    -> Load()
"""

''.endswith('')
