"""
SetComp astroid node

This node represents set comprehension expressions in Python, which take the
form {element for increment in iterable}. This node also makes use of the
Comprehension node.

Attributes:
    - elt         (Expr)
        - The part to be evaluated to make every item in the set. This can
          be any expression node, such as a BinOp or Str.
    - generators  (list[Comprehension])
        - This list contains one Comprehension node for every "for" clause
          in this set comprehension.

Example 1:
    SetComp(
        elt=BinOp(
            op='*',
            left=Name(name='x'),
            right=Const(value=2)),
        generators=[Comprehension(
            is_async=0,
            target=AssignName(name='x'),
            iter=List(
                ctx=<Context.Load: 1>,
                elts=[Const(value=1)]),
            ifs=[])])

Example 2:
    SetComp(
        elt=BinOp(
            op='*',
            left=Name(name='x'),
            right=Name(name='y')),
        generators=[Comprehension(
            is_async=0,
            target=AssignName(name='x'),
            iter=List(
                ctx=<Context.Load: 1>,
                elts=[
                    Const(value=0),
                    Const(value=1),
                    Const(value=2)]),
            ifs=[]),
            Comprehension(
                is_async=0,
                target=AssignName(name='y'),
                iter=List(
                    ctx=<Context.Load: 1>,
                    elts=[
                        Const(value=4),
                        Const(value=3),
                        Const(value=2)]),
                ifs=[Compare(
                    left=Name(name='x'),
                    ops=[['<', Name(name='y')]])])])

Type-checking:
    The type of the SetComp is set[T], where T is the type of elt.
"""

# Example 1
{x * 2 for x in [1]}

# Example 2
{x * y for x in [0, 1, 2] for y in [4, 3, 2] if x < y}
