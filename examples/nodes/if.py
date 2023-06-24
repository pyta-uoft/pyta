"""
If astroid node

An if statement.

Attributes:
    - test      (NodeNG)
        - Holds the node to evaluate such as Compare.
    - body      (list[NodeNG])
        - A list of nodes that will execute if the test condition passes.
    - orelse    (list[NodeNG])
        - A list of nodes executed when the test condition fails.
        - elif statements are nested inside of the orelse

Example 1:
    If(
        test=Compare(
            left=Name(name='n'),
            ops=[['==', Const(value=0)]]),
        body=[Pass()],
        orelse=[If(
                test=Name(name='something'),
                body=[Pass()],
                orelse=[If(
                        test=Compare(
                            left=Name(name='n'),
                            ops=[['>', Const(value=0)]]),
                        body=[Pass()],
                        orelse=[Assign(
                            targets=[AssignName(name='n')],
                            value=Const(value=3))])])])

Example 2:
    If(
        test=Compare(
            left=Name(name='n'),
            ops=[['==', Const(value=0)]]),
        body=[Expr(value=Call(
                func=Name(name='print'),
                args=[Const(value=1)],
                keywords=None)),
            Expr(value=Call(
                func=Name(name='print'),
                args=[Const(value=10)],
                keywords=None))],
        orelse=[Expr(value=Call(
                func=Name(name='print'),
                args=[Const(value=100)],
                keywords=None))])

Example 3:
    If(
        test=Compare(
            left=Name(name='x'),
            ops=[['==', Const(value=2)]]),
        body=[Pass()],
        orelse=[If(
                test=Compare(
                    left=Name(name='y'),
                    ops=[['==', Const(value=3)]]),
                body=[Pass()],
                orelse=[])])

Example 4
    If(
        test=Compare(
            left=Name(name='x'),
            ops=[['==', Const(value=5)]]),
        body=[Pass()],
        orelse=[])

"""

# Example 1
if n == 0:
    pass
elif something:
    pass
elif n > 0:
    pass
else:
    n = 3

# Example 2
if n == 0:
    print(1)
    print(10)
else:
    print(100)

# Example 3
if x == 2:
    pass
elif y == 3:
    pass

if x == 5:
    pass
