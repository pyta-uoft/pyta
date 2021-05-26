"""
Name astroid node

This node is used to represent variables in Python, in the context of Loading
the variable's contents. For Storing and Deleting, see AssignName and DelName.

Attributes:
    - name  (str)
        - The name of the variable.

Example:
    Name(name='my_var')

Type-checking:
    - The type of a name is determined by looking it up in the *type environment* of its
      enclosing scope.
"""

my_var
