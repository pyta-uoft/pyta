"""
List astroid node

This node represents the Python list objects.

Attributes:
    - elts  (list[Expr])
        - The elements in this list, which can be any expression.
    - ctx   (Context)
        - The context in which this list is to be used, either Load or Store.

Example 1:
    List(
        ctx=<Context.Load: 1>,
        elts=[])

Example 2:
    List(
        ctx=<Context.Load: 1>,
        elts=[
            Const(value=1),
            Const(value=2),
            Const(value=3)])

Example 3:
    Assign(
        targets=[List(
                ctx=<Context.Store: 2>,
                elts=[AssignName(name='x'), AssignName(name='y')])],
        value=Tuple(
            ctx=<Context.Load: 1>,
            elts=[Const(value=7), Const(value=8)]))

Example 3 demonstrates a Store context instead of Load


Type-checking:
    Type is list[T], where T is the most specific class that every element
    of the list is an instance of.
"""

# Example 1
[]

# Example 2
[1, 2, 3]

# Example 3
[x, y] = 7, 8
