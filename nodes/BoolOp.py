"""
BoolOp astroid node

A boolean operation, 'or' or 'and'.

Attributes:
    - values  ([Expr])
        - A list of the argument expressions
    - op      (str)
        - The operator, 'or' or 'and'.

Example 1:
    - values  -> [Const(value=None), Const(value=1)]
    - op      -> 'or'

Example 2:
    - values  -> [Const(value=None), Const(value=1), Const(value=2)]
    - op      -> 'or'

Example 3:
    - values  -> [Const(value=None), BoolOp(op='and', values=[Const(value=1),
                  Const(value=2)])]
    - op      -> 'or'

Type-checking:
    If all of the values have the type type, that type is used as the type of the of BoolOp itself.
    Otherwise, the type of the BoolOp is Any.
"""

# Example 1
None or 1

# Example 2
None or 1 or 2

# Example 3
None or 1 and 2
