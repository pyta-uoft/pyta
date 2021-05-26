"""
ListComp astroid node

This node represents list comprehension expressions in Python, which take the
form [element for increment in iterable]. This node also makes use of the
Comprehension node.

Attributes:
    - elt         (Expr)
        - The part to be evaluated to make every item in the list. This can
          be any expression node, such as a BinOp or Str.
    - generators  (list[Comprehension])
        - This list contains one Comprehension node for every "for" clause
          in this list comprehension.

Example 1:
    ListComp(
        elt=BinOp(
            op='+',
            left=Name(name='l'),
            right=Name(name='l')),
        generators=[Comprehension(
            is_async=0,
            target=AssignName(name='l'),
            iter=Const(value='str'),
            ifs=[])])

Example 2:
    ListComp(
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
                    Const(value=1),
                    Const(value=2),
                    Const(value=3)]),
            ifs=[]),
            Comprehension(
                is_async=0,
                target=AssignName(name='y'),
                iter=List(
                    ctx=<Context.Load: 1>,
                    elts=[
                        Const(value=4),
                        Const(value=5),
                        Const(value=6)]),
                ifs=[])])

Type-checking:
    The type of the ListComp is list[T], where T is the type of elt.
"""

# Example 1
[l+l for l in "str"]

# Example 2
[x*y for x in [1, 2, 3] for y in [4, 5, 6]]
