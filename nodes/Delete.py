"""
Delete astroid node

Delete node represents a del statement.

Attributes:
    - targets  (List[DelName | DelAttr | assignable])
        - The targets to be deleted. These must have a Del expression context,
          such as DelName and DelAttr themselves, or any assignable node
          except AssignName and AssignAttr. (See the README for more details.)

Example:
    - targets  -> [x]
"""

del x
