"""
BoolOp astroid node

A boolean operation, 'or' or 'and'.

Attributes:
    - op      (Optional[str])
        - The operator, 'or' or 'and'.
    - values  (Optional[list[Expr]])
        - A list of the argument expressions

Example 1:
    BoolOp(
        op='or',
        values=[Const(value=None), Const(value=1)])

Example 2:
    BoolOp(
        op='or',
        values=[Const(value=None), Const(value=1), Const(value=2)])

Example 3:
    BoolOp(
        op='or',
        values=[
            Const(value=None),
            BoolOp(
                op='and',
                values=[Const(value=1), Const(value=2)])])
"""

# Example 1
None or 1

# Example 2
None or 1 or 2

# Example 3
None or 1 and 2
