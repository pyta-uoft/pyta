"""
AsyncFunctionDef astroid node

Subclass of FunctionDef astroid node. An async def function definition and used
for async astroid nodes like AsyncFor and AsyncWith.

Example:
    - name        -> "func"
    - args        -> arg
    - doc         -> "This is function animal."
    - body        -> [Assign(dog, "an animal")]
    - decorators  -> @wrapper
    - returns     -> return dog
"""

@wrapper
def animal(arg):
    """
    This is function animal.
    """
    dog = "an animal"
    return dog
