"""
AnnAssign astroid node

A node representing an annotated assignment statement.

Attributes:
    - annotation    (NodeNG)
        - A Name node representing the type of the variable.
    - simple        (int)
        - Whether target is a pure name or complex statement.
    - target        (Optional[NodeNG])
        - An AssignName node representing the name of the variable being
        assigned to.
    - value         (Optional[Expr])
        - An node that is being assigned to the variables.

Example:
    AnnAssign(
        simple=1,
        target=AssignName(name='x'),
        annotation=Name(name='int'),
        value=Const(value=3))
"""


class Student:
    x: int = 3  # This is the example
