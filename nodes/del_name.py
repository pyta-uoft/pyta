"""
DelName astroid node

The name of an object being deleted.
This is a Name astroid node that specifically appears in the Del
(being deleted) context.

Attributes:
    - name: Optional[str]
        - The name of the object being deleted.

DelName can be initialized without a name (defaulting to None)

Example 1:
    - DelName(name='x')
"""

# Example 1
del x
