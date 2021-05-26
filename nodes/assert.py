"""
Assert astroid node

An assertion.

Attributes:
    - fail  (Optional[NodeNG])
        - A message that is shown when the assertion fails.
    - test  (Optional[Expr])
        - This holds the condition, such as a Compare node, to be evaluated
          True or False

Example:
    Assert(
        test=Compare(
            left=Name(name='x'),
            ops=[['==', Const(value=0)]]),
        fail=Const(value='error'))
"""

assert x == 0, 'error'
