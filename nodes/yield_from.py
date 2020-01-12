"""
YieldFrom astroid node

This node represents the Python "yield from" statement, which functions
similarly to the "yield" statement except that the generator can delegate
some generating work to another generator.

Attributes:
    - value  (Expr)
        - The generator that this YieldFrom is delegating work to,
          which must be a generator expression (either a GeneratorExp node
          or an Expr node containing a generator expression).

Example:
    - value  -> Call(range, Name('g'))
"""

def fun(g):
    yield from range(g)
