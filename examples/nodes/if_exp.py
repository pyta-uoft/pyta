"""
IfExp astroid node

An if statement written in an expression form.
(IfExp node represents an expression, not a statement.)

Attributes:
    - test      (NodeNG)
        - Holds a single node such as Compare to evaluate the truth condition of.
    - body      (NodeNG)
        - A Node representing the suite to be executed when the if expression
          evalutes to True.
    - orelse    (NodeNG)
        - The Node representing the suite to be executed when the if expression
          evaluates to False.

Example 1:
    IfExp(
        test=Const(value=True),
        body=Const(value=1),
        orelse=Const(value=0))

Example 2:
    IfExp(
    test=Compare(
        left=Name(name='eval_expr'),
        ops=[['==', Name(name='expected')]]),
    body=BinOp(
        op='+',
        left=Name(name='x'),
        right=Name(name='y')),
    orelse=Name(name='something'))


Type-checking:
    The type of the expression is the same as the type of the body and orelse expressions
    (they must have the same type).
"""

# Example 1
1 if True else 0

# Example 2
x + y if eval_expr == expected else something
