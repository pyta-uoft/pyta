"""
Await astroid node

An await expression. Only valid in the body of an AsyncFunctionDef.

Attributes:
    - value     (Optional[Expr])
        - What the expression waits for.

Example:
    Await(
        value=Call(
            func=Name(name='async_coroutine'),
            args=[],
            keywords=None))
"""


def async_coroutine():
    pass


async def fun():
    await async_coroutine()
