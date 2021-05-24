"""
With astroid node

This node represents the Python "with" statement, which is used to simplify
set up/tear down actions for a block of code.

Attributes:
    - items  (list[tuple[Expr]])
        - The expressions or expression-reassigned Name pairs that are to be
          set up by this "with" and torn down after the completion of body.
          Expressions are usually Call or Name nodes.
    - body   (list[Statement])
        - The code to be performed until the with statement closes.

Example 1:
    With(
        items=[[Call(
            func=Name(name='open'),
            args=[Subscript(
                ctx=<Context.Load: 1>,
                value=Attribute(
                    attrname='argv',
                    expr=Name(name='sys')),
                slice=Const(value=1))],
            keywords=None),
            AssignName(name='f')],
            [Call(
                func=Name(name='open'),
                args=[Const(value='input.txt')],
                keywords=None),
                AssignName(name='i')]],
        body=[Pass()])
"""

with open(sys.argv[1]) as f, open('input.txt') as i:
    pass
