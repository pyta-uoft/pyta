"""
Yield astroid node

This node represents the Python "yield" statement, which turns a function
into a generator object that returns the "yielded" results iteratively as
needed by the calling program.

Attributes:
    - value  (Optional[Expr])
        - Optionally, the value to be yielded.

Example 1:
    Yield(value=None)

Example 2:
    Yield(value=Const(value=None))

Example 3:
    Yield(value=Name(name='x'))
"""

# Example 1
yield

# Example 2
yield None

# Example 3
yield x
