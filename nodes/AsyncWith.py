"""
AsyncWith astroid node

Similar to AsyncFor. Asynchronous code doesn't wait for an operation to
complete, rather the code executes all operations in one go. Only valid in body
of an AsyncFunctionDef astroid node.

Attributes:
    - items  (List[Withitem])
        - Represents context managers.
    - body   (List[Node])
        - The indented block inside the context. Contains lists of nodes to
          execute.

Example:
    - items  -> open('/foo/bar', 'r')
    - body   -> pass
"""

async def fun():
    async with open('/foo/bar', 'r') as f:
        pass
