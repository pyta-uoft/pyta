"""
AsyncFor astroid node

Subclass of For astroid node. This node iterates over async code with a for-loop
 like syntax. Asynchronous code doesn't wait for an operation to complete,
 rather the code executes all operations in one go. Only valid in body of an
 AsyncFunctionDef astroid node.

 Example:
     - target  -> i
     - iter    -> i in range(3)
     - body    -> pass
     - orelse  -> None
"""

async def fun():
    """Note coroutine function must be declared with async def."""
    async for i in range(3):
        pass
