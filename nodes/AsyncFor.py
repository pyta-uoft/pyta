"""
AsyncFor astroid node

This node iterates over async code with a for-loop like syntax. Asynchronous
code doesn't wait for an operation to complete, rather the code executes all
operations in one go. Only valid in body of an AsyncFunctionDef astroid node.

Attributes:
    - target  (Node(Name|Tuple|List))
        - Initial value for the iteration variable and may be any type,
          not just a number. Equivalent to for loop's i = 0.
    - iter    (Node)
        - Holds the item to be looped over.
    - body    (List[Node])
        - Contains lists of nodes to execute.
    - orelse  (List[Node])
        - Will execute if the loop finished normally rather than via a
          break statement.

Example:
    - target  -> i
    - iter    -> range(3)
    - body    -> [pass]
    - orelse  -> None
"""

async def fun():
    """Note coroutine function must be declared with async def."""
    async for i in range(3):
        pass
