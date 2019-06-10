"""
DelName astroid node

Represents when an object is being deleted.
This is a Name astroid node that specifically appears in the Del
(being deleted) context.

Attributes:
    - name  (Name)
        - The node being deleted.

Example:
    - name  -> DelName(name='x')
"""

del x
