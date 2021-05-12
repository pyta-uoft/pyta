"""
Slice astroid node

This node represents the Python slicing operator, used to isolate parts of
an iterable. It is used in the Subscript node.

Attributes:
    - lower  (NodeNG (Expr))
        - The optional lower bound of this slice, which must evaluate to an
          integer. Default: 0.
    - upper  (NodeNG (Expr))
        - The optional upper bound (non-inclusive) of this slice, which must
          evaluate to an integer. Default: length of the iterable being sliced.
    - step   (NodeNG (Expr) | None)
        - The optional step (number of iterations to skip) for this slice,
          which must evaluate to an integer. Default: None.

Example 1: (Nested in Subscript node)
    - Subscript(
       ctx=<Context.Load: 1>,
       value=Name(name='a'),
       slice=Slice( # Slice node
          lower=None,
          upper=None,
          step=None))

Example 2: (Nested in Subscript node)
    - Subscript(
       ctx=<Context.Load: 1>,
       value=Name(name='a'),
       slice=Slice( # Slice node
          lower=Const(value=1),
          upper=None,
          step=None))

Example 3: (Nested in Subscript node)
    - Subscript(
       ctx=<Context.Load: 1>,
       value=Name(name='a'),
       slice=Slice( # Slice node
          lower=Const(value=1),
          upper=UnaryOp(
             op='-',
             operand=Const(value=1)),
          step=Const(value=3)))

Type-checking:
    Delegate to the __init__ constructor for slice, setting type to 'slice' on success.
"""

# Example 1
a[:]

# Example 2
a[1:]

# Example 3
a[1:-1:3]
