"""
AsyncWith astroid node

Subclass of With astroid node, which is used to simplify set up/tear down
actions for a block of code. Asynchronous code doesn't wait for an operation
to complete, rather the code executes all operations in one go. Only valid in
body of an AsyncFunctionDef astroid node.

Attributes:
    - # Derives directly from "With" node; see "with" node for attributes.

Example:
    AsyncWith(
        items=[
            [
                Call(
                    func=Name(name='open'),
                    args=[Const(value='/foo/bar'), Const(value='r')],
                    keywords=None),
                AssignName(name='f')]],
        body=[Pass()])
"""


async def fun():
    async with open('/foo/bar', 'r') as f:
        pass
