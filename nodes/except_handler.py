"""
ExceptHandler astroid node

ExceptHandler is a single except clause.

Attributes:
    - type: Optional[Union[tuple, NodeNG]]
        - Typically a Name node like ValueError or TypeError.
    - name: Optional[AssignName]
        - The AssignName to pass the error to (can be None for no assignable)
    - body: Optional[list[NodeNG]]
        - A list of nodes in the body of the exception.

Full Example:
    TryExcept(
       body=[Pass()],
       handlers=[ExceptHandler(
             type=Name(name='ValueError'),
             name=AssignName(name='e'),
             body=[Pass()])],
       orelse=[])

Example 2:
    TryExcept(
       body=[Pass()],
       handlers=[ExceptHandler(
             type=Name(name='AssertionError'),
             name=None,
             body=[Pass()])],
       orelse=[])
"""

# Example 1
try:
    pass
except ValueError as e:
    pass

# Example 2
try:
    pass
except AssertionError:
    pass
