"""
Subscript astroid node

This node represents iterable subscripting using '[' and ']' in Python.

Attributes:
    - value  (Expr)
        - The iterable whose elements are to be accessed by the subscript.
    - slice  (Expr)
        - The index or slice of the iterable being subscripted.
    - ctx    (class[expr_context])
        - The context in which this subscripted iterable is used, one of
          Load, Store, or Del.

Example:
    Subscript(
        ctx=<Context.Load: 1>,
        value=Name(name='x'),
        slice=Const(value=0))
"""

x[0]
