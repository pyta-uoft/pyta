"""
Await astroid node

An await expression. Only valid in the body of an AsyncFunctionDef.

Attributes:
    - value  (Node)
        - What the expression waits for.

Example:
    - value  -> pass
"""

def async_coroutine():
    pass

async def fun():
    await async_coroutine()
