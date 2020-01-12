async def fun():
    """Note coroutine function must be declared with async def."""
    async for a in b:
        if a > 5:
            break
    else:
        continue
