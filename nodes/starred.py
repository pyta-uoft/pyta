"""
Starred astroid node

This node represents a starred variable reference, used for unpacking iterables
into lists. This type of node usually appears under a List, Tuple, or Call node.

Attributes:
    - value    (Name)
        - The variable to be unpacked into as a list.
    - ctx      (class[expr_context])
        - The context in which this starred variable is used, one of
          Load or Store.

Example 1: (nested in Tuple)
    Assign(
        targets=[Tuple(
            ctx=<Context.Store: 2>,
            elts=[Starred(
                ctx=<Context.Store: 2>,
                value=AssignName(name='a')),
                AssignName(name='b')])],
        value=Call(
            func=Name(name='range'),
            args=[Const(value=5)],
            keywords=None))

Example 2: (nested in Call)
    Call(
        func=Name(name='print'),
        args=[Starred(
            ctx=<Context.Load: 1>,
            value=Name(name='x'))],
        keywords=None)
"""

# Example 1
*a, b = range(5)

# Example 2
print(*x)
