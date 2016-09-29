"""
Await astroid node

An await expression. Only valid in the body of an AsyncFunctionDef.

Attributes:
    - value  (Node)
        - What Await astroid node waits for.

Example:
    - value  -> [to be filled]
"""

def async_coroutine():
    pass

async def fun():
    await async_coroutine()
