"""
YieldFrom astroid node

This node represents the Python "yield from" statement, which functions
similarly to the "yield" statement except that the generator can delegate
some generating work to another generator.

Attributes:
    - value  (GeneratorExp)
        - The generator that this YieldFrom is delegating work to.

Example:
    - value  -> Call(range, Name('g', Load()))
"""

def fun(g):
    yield from range(g)
