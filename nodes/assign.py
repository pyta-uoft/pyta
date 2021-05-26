"""
Assign astroid node

An assignment.

Attributes:
    - targets           (Optional[list[NodeNG]])
        - A list of nodes being assigned to.
    - type_annotation   (Optional[NodeNG])
        - If present, this will contain the type annotation passed by a type comment.
    - value             (Optional[Expr])
        - The value being assigned to the variables.

Example 1:
    Assign(
        targets=[AssignName(name='x')],
        value=Const(value=3))

Example 2:
    Assign(
        targets=[
            AssignName(name='a'),
            AssignName(name='b')],
        value=Const(value=1))

Example 3:
    Assign(
        targets=[
            Tuple(
                ctx=<Context.Store: 2>,
                elts=[AssignName(name='a'), AssignName(name='b')])],
        value=Name(name='c'))

Example 4:
    Assign(
        targets=[List(
                ctx=<Context.Store: 2>,
                elts=[AssignName(name='a'), Starred(
                        ctx=<Context.Store: 2>,
                        value=AssignName(name='b'))])],
        value=Name(name='d'))

Type-checking:
    - Single identifiers are associated with the type of the expression on the RHS of the =.
    - For (unpacking) tuple/list assignment, the RHS must be an iterable of the same length as
      the number of identifiers on the LHS.
    - An exception is when the * operator is used preceding a variable,
      in this case, the remaining values in the iterable will assigned to
      that variable as a list.
"""

# Example 1
x = 3

# Example 2
a = b = 1

# Example 3
a, b = c

# Example 4
[a, *b] = d
