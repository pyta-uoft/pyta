"""
ExceptHandler astroid node

Attributes:
    - type  (node)  typically a Name node or None for a catch-all "except:"
    clause
    - name  (str)   a raw string for the name to hold the exception
    - body  (list)  a list of nodes

Example:
    - type  -> None
    - name  -> None
    - body  -> [pass]
"""

try:
    pass
except:
    pass
