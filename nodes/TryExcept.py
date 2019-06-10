"""
TryExcept astroid node

This node is used to represent the try-except statements for handling
exceptions in Python, which may also include an "else" block.

Attributes:
    - body      (List[Statement])
        - The code to be executed under the "try" statement to check for
          any raised exceptions.
    - handlers  (List[ExceptHandler])
        - The exceptions to be handled (including the code to handle them)
          if raised by code in the "try" block. (One ExceptHandler per "except"
          block.)
    - orelse    (List[Statement])
        - Optionally, the code to be executed if the "try" code does not
          raise any exceptions.

Example 1:
    - body      -> [Pass()]
    - handlers  -> [ExceptHandler(body=[Pass])]
    - orelse    -> []

Example 2:
    - body      -> [Pass()]
    - handlers  -> [ExceptHandler(body=[Pass])]
    - orelse    -> [Pass()]
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
