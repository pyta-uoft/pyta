"""
TryExcept astroid node

This node is used to represent the try-except statements for handling
exceptions in Python, which may also include an "else" block.

Attributes:
    - body      (list[Statement])
        - The code to be executed under the "try" statement to check for
          any raised exceptions.
    - handlers  (list[ExceptHandler])
        - The exceptions to be handled (including the code to handle them)
          if raised by code in the "try" block. (One ExceptHandler per "except"
          block.)
    - orelse    (list[Statement])
        - Optionally, the code to be executed if the "try" code does not
          raise any exceptions.

Example 1:
    TryExcept(
        body=[Pass()],
        handlers=[ExceptHandler(
            type=None,
            name=None,
            body=[Pass()])],
        orelse=[])

Example 2:
    TryExcept(
        body=[Pass()],
        handlers=[ExceptHandler(
            type=None,
            name=None,
            body=[Pass()])],
        orelse=[Pass()])
"""

# Example 1
try:
    pass
except:
    pass

# Example 2
try:
    pass
except:
    pass
else:
    pass
