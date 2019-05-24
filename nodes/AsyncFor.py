"""
AsyncFor astroid node

Subclass of For astroid node. This node iterates over async code with a for-loop
 like syntax. Asynchronous code doesn't wait for an operation to complete,
 rather the code executes all operations in one go. Only valid in body of an
 AsyncFunctionDef astroid node.

Attributes:
    - target  (Name | Tuple | List)
        - Holds the variable(s) the loop assigns to as a single node.
    - iter    (Node)
        - The single node to be looped over.
    - body    (List[Node])
        - The node to be executed.
    - orelse  (List[Node] | None)
        - Node will execute if the loop finished normally rather than via a
        break statement.

 Example:
     - target  -> AssignName(name='a')
     - iter    -> Name(name='b')
     - body    -> [If(test=Compare(left=Name(id='a'), ops=[['>', Const(value=5)]]),
                   body=[Break()], orelse=[])]
     - orelse  -> [Continue()]
"""

async def fun():
    """Note coroutine function must be declared with async def."""
    async for a in b:
        if a > 5:
            break
    else:
        continue
