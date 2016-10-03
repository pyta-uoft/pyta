"""
AsyncWith astroid node

Subclass of With astroid node. Asynchronous code doesn't wait for an operation
to complete, rather the code executes all operations in one go. Only valid in
body of an AsyncFunctionDef astroid node.
"""

async def fun():
    async with open('/foo/bar', 'r') as f:
        pass
