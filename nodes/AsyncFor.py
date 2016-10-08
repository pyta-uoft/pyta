"""
AsyncFor astroid node

Subclass of For astroid node. This node iterates over async code with a for-loop
 like syntax. Asynchronous code doesn't wait for an operation to complete,
 rather the code executes all operations in one go. Only valid in body of an
 AsyncFunctionDef astroid node.

Attributes:
    - target  (Node(Name | Tuple | List))
        - Holds the variable(s) the loop assigns to as a single node.
    - iter    (Node)
        - The node to be looped over.
    - body    (Node)
        - The node to be executed.
    - orelse  (Node)
        - Node will execute if the loop finished normally rather than via a
        break statement.

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
