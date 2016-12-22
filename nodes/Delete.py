"""
Delete astroid node

Delete node represents a del statement.

Attributes:
    - targets  (List[DelName | DelAttr | Subscript | assignable])
        - The targets to be deleted. These must have a Del expression context,
          such as DelName and DelAttr themselves, or any assignable node
          except AssignName and AssignAttr. (See the README for more details.)

Example 1:
    - targets  -> [DelName(x)]

Example 2:
    - targets  -> [DelName(x), DelAttr(Name("self", Del()), "attr"),
                  Subscript(Name(y), Index(0), Del)]
"""

# Example 1
del x

# Example 2
del x, self.attr, y[0]
