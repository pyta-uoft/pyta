"""
Delete astroid node

Delete node represents a del statement.

Attributes:
    - targets  (List[Node])
        - The targets to be deleted of type Name, Attributes, or Subscript
          nodes.

Example:
    - targets  -> [x]
"""

del x
