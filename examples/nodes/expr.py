"""
Expr astroid node

When an expression, such as a function call, appears as a statement by itself
with its return value not used or stored, it is wrapped in Expr node.

Attributes:
    - value  (NodeNG)
        - Value holds nodes like Name, Lambda, Yield or YieldFrom.

Examples:

    Expr(value=Call(
        func=Name(name='print'),
        args=[Const(value=1)],
        keywords=None))

    Expr(value=BinOp(
        op='*',
        left=Const(value=100),
        right=Const(value=42)))

    Expr(value=Const(value=0))

    Expr(value=Tuple(
        ctx=<Context.Load: 1>,
        elts=[Const(value=1), Const(value=2)]))

    Expr(value=Subscript(
        ctx=<Context.Load: 1>,
        value=Const(value='a'),
        slice=Const(value=0)))

    Expr(value=Subscript(
        ctx=<Context.Load: 1>,
        value=Dict(items=[[Const(value='a'), Const(value=0)], [Const(value='b'), Const(value=1)]]),
        slice=Const(value=0)))
"""

# Examples
print(1)
100 * 42
0
(1, 2)
"a"[0]
(1, 2)[0]
[1, 2, 3][0]
{"a": 0, "b": 1}[0]
