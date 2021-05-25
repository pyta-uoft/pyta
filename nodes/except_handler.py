"""
ExceptHandler astroid node

ExceptHandler is a single except clause.

Attributes:
    - type  (Optional[NodeNG | tuple])
        - Typically a Name node like ValueError or TypeError.
    - name  (Optional[AssignName])
        - The AssignName to pass the error to (can be None for no assignable)
    - body  (list[NodeNG])
        - A list of nodes in the body of the exception.

Example 1:
    TryExcept(
        body=[Pass()],
        handlers=[ExceptHandler(
            type=None,
            name=None,
            body=[Pass()])],
        orelse=[])

* ExceptHandler is in the handlers list of the TryExcept node

Example 3:
    TryExcept(
        body=[Pass()],
        handlers=[ExceptHandler(
            type=Name(name='AssertionError'),
            name=None,
            body=[Pass()])],
        orelse=[])

Example 2:
    TryExcept(
        body=[Pass()],
        handlers=[ExceptHandler(
                type=Name(name='ValueError'),
                name=AssignName(name='e'),
                body=[Pass()])],
        orelse=[])

Example 4:
    TryExcept(
       body=[Pass()],
       handlers=[ExceptHandler(
             type=Tuple(
                ctx=<Context.Load: 1>,
                elts=[Name(name='AssertionError'), Name(name='ValueError')]),
             name=AssignName(name='e'),
             body=[Pass()])],
       orelse=[])

"""

# Example 1
try:
    pass
except:
    pass

# Example 2
try:
    pass
except AssertionError:
    pass

# Example 3
try:
    pass
except ValueError as e:
    pass

# Example 4
try:
    pass
except (AssertionError, ValueError) as e:
    pass
