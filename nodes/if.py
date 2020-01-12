"""
If astroid node

An if statement.

Attributes:
    - test    (Node)
        - Holds a single node such as Compare.
    - body    (List[Node])
        - A list of nodes that will execute if the condition passes.
    - orelse  (List[Node])
        - The else clause. Also, elif clauses don’t have a special
          representation so it appears as If nodes within orelse.

Example:
    - test    -> Compare(left=Name(name='n'), ops=[['==', Const(value=0)]])
    - body    -> [Pass()]
    - orelse  -> [If(Name(name='something'), Pass(),
                     If(Compare(n > 0), Pass(), n=3]))]
"""

if n == 0:
    pass
elif something:
    pass
elif n > 0:
    pass
else:
    n = 3
