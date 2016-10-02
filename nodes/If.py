"""
If astroid node

An if statement.

Attributes:
    - test    (Node)
        - Holds a single node such as Compare.
    - Body    (List[Node])
        - A list of nodes that will execute if the condition passes.
    - orelse  (List[Node])
        - The else clause. Also, elif clauses don’t have a special
          representation so it appears as If nodes within orelse.

Example:
    - test    -> n == 0
    - Body    -> [pass]
    - orelse  -> [If(n > 0, pass, None), n = 3]
"""

if n == 0:
    pass
elif n > 0:
    pass
else:
    n = 3

