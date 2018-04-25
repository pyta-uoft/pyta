"""
Compare astroid node

Compare node represents a value comparison between two objects, which do not need to have the same type.
Value comparison operators are: '<', '>', '==', '<=', '>=', '!="
Expressions are always evaluated at most once (PRIOR to comparison) and the values are stored as attributes in the node.
Multi-comparison expressions are logically equivalent to the conjunction of the individual value comparisons.

Attributes:
    - left  (value)
        - The first value in the comparison.
    - ops   (List[Tuple(str, value)])
        - The list of operators to be performed on left.

Example:
    - left  -> Const.int(value=0)
    - ops   -> [('<', Const.int(value=1)), ('!=", Const.int(value=1))]

Type-checking:
    An individual comparison is converted to its corresponding method and type-checked.
    Multiple comparisons in a single expression are type-checked in left-to-right order.
    If each comparison returns the same type, that type is set for the entire Compare node.
    Otherwise, the type of the Compare node is Any.
"""

0 < 1 != 1

1 > 3

b'5' <= b'6'

'bob' == 'bob' != 'george'
