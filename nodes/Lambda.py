"""
Lambda astroid node

Lambda is a minimal function definition that can be used inside an expression.

Attributes:
    - args    (Arguments)
        - The arguments for function lambda.
    - body    (Node)
        - The body of function lambda. The body should be a single node.

Example 1:
    - args    -> Arguments()
    - body    -> Const(value=3)

Example 2:
    - args    -> Arguments(args=[AssignName(name='x'), AssignName(name='y')])
    - body    -> BinOp(op='+', left=Name(name='x'), right=Name(name='y'))

Type-checking:
    The inferred type is a Callable with arguments inferred from the body of the
    lambda expressions and whose return type is the inferred type of the body.
"""

# Example 1
fun = lambda: 3

# Example 2
fun2 = lambda x, y: x + y
