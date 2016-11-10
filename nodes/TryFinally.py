"""
TryFinally astroid node

This node is used to represent the try-finally statements for handling
exceptions in Python along with teardown code, and may also include
an "except" block (with optional "else") that is handled by TryExcept nodes.

Attributes:
    - body      (List[Statement])
        - The code to be executed under the "try" statement to check for
          any raised exceptions. If this TryFinally also has an "except" block,
          body will consist of TryExcept node(s) that also hold the "try" code.
    - finalbody (List[Statement])
        - The code to be executed after the "try" block, regardless of
          whether any exceptions were raised.

Example:
    - body       -> TryExcept(body=[Pass], handlers=ExceptHandler[body=Pass],
                               orelse=[])]
    - finalbody  -> [Pass]
"""

try:
    pass
except:
    pass
finally:
    pass
