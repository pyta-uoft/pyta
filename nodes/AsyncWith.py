"""
AsyncWith astroid node

Subclass of With astroid node, which is used to simplify set up/tear down
actions for a block of code. Asynchronous code doesn't wait for an operation
to complete, rather the code executes all operations in one go. Only valid in
body of an AsyncFunctionDef astroid node.

Attributes:
    - items  (List[Expr])
        - The expressions or expression-reassigned Name pairs that are to be
          set up by this "with" and torn down after the completion of body.
          Expressions are usually Call or Name nodes.
    - body   (List[Statement])
        - The code to be performed until the with statement closes.

Example:
    - items  -> [Call(open('/foo/bar', 'r'), Name('f', Load())]
    - body   -> [Node(Pass)]
"""

async def fun():
    async with open('/foo/bar', 'r') as f:
        pass
