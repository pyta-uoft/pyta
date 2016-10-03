"""
Raise astroid node

This node represents the "raise" statement in Python, which is used to raise
exceptions. This statement also handles exception chaining using the "from"
clause, which is included in the Raise node.

Attributes:
    - exc    (Node | None)
        - The exception to be raised, either a Call or Name node. Can also
          be None for standalone "raise" statements.
    - cause  (Node)
        - This optional attribute allows explicit declaration of the
          originating exception, using a Call or Name exception node.

Example 1:
    - exc    -> Call("ZeroDivisionError")

Example 2:
    - exc    -> Call("RuntimeError", "Something bad happened")
    - cause  -> Name("exc")

Example 3:
    - exc    -> Call("RuntimeError", "Something bad happened")
    - cause  -> None
"""

# Example 1
# Prints context traceback by default.
try:
    print(1 / 0)
except Exception:
    raise ZeroDivisionError()

# Example 2 (taken from Python docs)
# Prints context traceback, explicitly states "direct cause".
try:
    print(1 / 0)
except Exception as exc:
    raise RuntimeError("Something bad happened") from exc

# Example 3
# Does not print context traceback.
try:
    print(1 / 0)
except Exception as exc:
    raise RuntimeError("Something bad happened") from None
