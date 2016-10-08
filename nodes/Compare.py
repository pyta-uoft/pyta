"""
Compare astroid node

A comparison of two or more values.

Attributes:
    - left  (Expr)
        - The first value in the comparison.
    - ops   (List[Expr])
        - The list of operators to be performed on left.

Example:
    - left  -> Name(id='3', ctx=Load())
    - ops   -> [Gt()]
"""

3 > 2
