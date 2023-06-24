"""
TryFinally astroid node

This node is used to represent the try-finally statements for handling
exceptions in Python along with teardown code, and may also include
an "except" block (with optional "else") that is handled by TryExcept nodes.

Attributes:
    - body      (list[Statement])
        - The code to be executed under the "try" statement to check for
          any raised exceptions. If this TryFinally also has an "except" block,
          body will consist of TryExcept node(s) that also hold the "try" code.
    - finalbody (list[Statement])
        - The code to be executed after the "try" block, regardless of
          whether any exceptions were raised.

Example:
    TryFinally(
        body=[TryExcept(
            body=[Pass()],
            handlers=[ExceptHandler(
                type=None,
                name=None,
                body=[Pass()])],
            orelse=[])],
        finalbody=[Pass()])
"""

try:
    pass
except:
    pass
finally:
    pass
