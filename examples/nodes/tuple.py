"""
Tuple astroid node

This node represents the Python tuple objects.

Attributes:
    - elts  (list[Expr])
        - The elements in this tuple, which can be any expression.
    - ctx   (class[expr_context])
        - The context in which this list is to be used, either Load or Store.

Example 1:
    Tuple(
        ctx=<Context.Load: 1>,
        elts=[])

Example 2:
    Tuple(
        ctx=<Context.Load: 1>,
        elts=[Const(value=1), Const(value=2)])

Example 3: (nested in Assign)
    Assign(
        targets=[Tuple(
            ctx=<Context.Store: 2>,
            elts=[AssignName(name='x'), AssignName(name='y')])],
        value=List(
            ctx=<Context.Load: 1>,
            elts=[Const(value=7), Const(value=8)]))
"""

# Example 1:
()

# Example 2:
(1, 2)

# Example 3:
(x, y) = [7, 8]
