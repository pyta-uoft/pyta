"""
Subscript astroid node

This node represents iterable subscripting using '[' and ']' in Python.

Attributes:
    - value  (Expr)
        - The iterable whose elements are to be accessed by the subscript.
    - slice  (Node[Index | Slice | ExtSlice])
        - The index or slice of the iterable being subscripted.
    - ctx    (class[expr_context])
        - The context in which this subscripted iterable is used, one of
          Load, Store, or Del.

Example:
    - value  -> Name('x', Load())
    - slice  -> Index(0)
    - ctx    -> Load

Type-checking:
    Delegates to the methods __getitem__, __setitem__, or __delitem__, depending on context.
"""

x[0]
