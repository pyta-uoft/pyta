"""
Delete astroid node

Delete node represents a del statement.

Attributes:
    - targets  (List[DelName | DelAttr | Subscript])
        - The targets to be deleted.

Example 1:
    - targets  -> [DelName(x)]

Example 2:
    - targets  -> [DelName(x), DelAttr(Name("self", del()), "attr"),
                  Subscript(Name(y), Index(0), del)]
"""

# Example 1
del x

# Example 2
del x, self.attr, y[0]
