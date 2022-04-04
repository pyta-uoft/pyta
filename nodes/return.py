"""
Return astroid node

This node represents the Python return statement, which can return any
expression from None to a function Call, or even cause the function to exit
without returning anything.

Attributes:
    - value  (Optional[Expr])
        - Optionally, the value to be returned, which can be any possible
          expression.

Example 1:
    Return(value=None)

Example 2:
    Return(value=Const(value=None))

Example 3:
    Return(value=ListComp(
        elt=BinOp(
            op='**',
            left=Name(name='x'),
            right=Const(value=2)),
        generators=[Comprehension(
            is_async=0,
            target=AssignName(name='x'),
            iter=Call(
                func=Name(name='range'),
                args=[Const(value=10)],
                keywords=None),
            ifs=[])]))
"""

# Example 1
return

# Example 2
return None

# Example 3
return [x**2 for x in range(10)]
