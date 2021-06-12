"""
AsyncFor astroid node

Subclass of For astroid node. This node iterates over async code with a for-loop
 like syntax. Asynchronous code doesn't wait for an operation to complete,
 rather the code executes all operations in one go. Only valid in body of an
 AsyncFunctionDef astroid node.

Attributes:
    # Derives directly from "For" node; see "For" node for attributes.

Example:
    AsyncFor(
        target=AssignName(name='a'),
        iter=Name(name='b'),
        body=[
            If(
                test=Compare(
                left=Name(name='a'),
                ops=[['>', Const(value=5)]]),
                body=[Break()],
                orelse=[])],
        orelse=[Continue()])

"""

async def fun():
    """Note coroutine function must be declared with async def."""
    async for a in b:
        if a > 5:
            break
    else:
        continue
