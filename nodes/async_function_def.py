"""
AsyncFunctionDef astroid node

Subclass of FunctionDef astroid node. An async def function definition and used
for async astroid nodes like AsyncFor and AsyncWith.

Attributes:
    # Derives directly from "FunctionDef" node; see "FunctionDef" node for attributes.

Example:
    AsyncFunctionDef(
        name='animal',
        doc='\n    This is function animal.\n    ',
        decorators=None,
        args=Arguments(
            vararg=None,
            kwarg=None,
            args=[AssignName(name='arg')],
            defaults=[],
            kwonlyargs=[],
            posonlyargs=[],
            posonlyargs_annotations=[],
            kw_defaults=[],
            annotations=[None],
            varargannotation=None,
            kwargannotation=None,
            kwonlyargs_annotations=[],
            type_comment_args=[None],
            type_comment_kwonlyargs=[],
            type_comment_posonlyargs=[]),
        returns=None,
        body=[
            Assign(
                targets=[AssignName(name='dog')],
                value=Const(value='an animal')),
                Return(value=Name(name='dog'))])

"""

@wrapper
async def animal(arg):
    """
    This is function animal.
    """
    dog = "an animal"
    return dog
