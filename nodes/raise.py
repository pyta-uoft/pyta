"""
Raise astroid node

This node represents the "raise" statement in Python, which is used to raise
exceptions. This statement also handles exception chaining using the "from"
clause, which is included in the Raise node.

Attributes:
    - exc    (Optional[Node[Call | Name]])
        - The exception to be raised, either a Call or Name node. Can also
          be None for standalone "raise" statements.
    - cause  (Optional[Node[Call | Name | Const]])
        - This optional attribute allows explicit declaration of the
          originating exception, using a Call, Name or Const exception node.

Example 1: (Nested in ExceptHandler)
    TryExcept(
        body=[Expr(value=Call(
            func=Name(name='print'),
            args=[BinOp(
                op='/',
                left=Const(value=1),
                right=Const(value=0))],
            keywords=None))],
        handlers=[ExceptHandler(
            type=Name(name='Exception'),
            name=None,
            body=[Raise(
                exc=Call(
                    func=Name(name='ZeroDivisionError'),
                    args=[],
                    keywords=None),
                cause=None)])],
        orelse=[])

Example 2: (Nested in ExceptHandler)
    TryExcept(
        body=[Expr(value=Call(
            func=Name(name='print'),
            args=[BinOp(
                op='/',
                left=Const(value=1),
                right=Const(value=0))],
            keywords=None))],
        handlers=[ExceptHandler(
            type=Name(name='Exception'),
            name=AssignName(name='exc'),
            body=[Raise(
                exc=Call(
                    func=Name(name='RuntimeError'),
                    args=[Const(value='Something bad happened')],
                    keywords=None),
                cause=Name(name='exc'))])],
        orelse=[])

Example 3: (Nested in ExceptHandler)
    TryExcept(
        body=[Expr(value=Call(
            func=Name(name='print'),
            args=[BinOp(
                op='/',
                left=Const(value=1),
                right=Const(value=0))],
            keywords=None))],
        handlers=[ExceptHandler(
            type=Name(name='Exception'),
            name=AssignName(name='exc'),
            body=[Raise(
                exc=Call(
                    func=Name(name='RuntimeError'),
                    args=[Const(value='Something bad happened')],
                    keywords=None),
                cause=Const(value=None))])],
        orelse=[])
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
