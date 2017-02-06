"""
Yield astroid node

This node represents the Python "yield" statement, which turns a function
into a generator object that returns the "yielded" results iteratively as
needed by the calling program.

Attributes:
    - value  (Expr | None)
        - Optionally, the value to be yielded.

Example 1:
    - value  -> None

Example 2:
    - value  -> Const(NoneType)

Example 3:
    - value  -> Name('x', Load())
"""

# Example 1
yield

# Example 2
yield None

# Example 3
yield x
