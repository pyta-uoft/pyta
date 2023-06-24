"""
DelName astroid node

The name of an object being deleted.
This is a Name astroid node that specifically appears in the Del
(being deleted) context.

Attributes:
    - name  (str)
        - The node being deleted.

Example 1:
    Delete(targets=[DelName(name='x')])

* DelName is in the targets list of the Delete node

"""

# Example 1
del x
