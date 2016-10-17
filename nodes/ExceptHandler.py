"""
ExceptHandler astroid node

ExceptHandler is a single except clause.

Attributes:
    - type  (Node)
        - Typically a Name node like ValueError or TypeError.
    - name  (str)
        - A raw string for the name to hold the exception.
    - body  (List[Node])
        - A list of nodes.

Example:
    - type  -> ValueError
    - name  -> 'e'
    - body  -> [pass]

"""

try:
    pass
except ValueError as e:
    pass
