"""
FunctionDef astroid node

This node represents a function definition.

Attributes:
    - name          (str)
        - The function's name.
    - args          (Arguments)
        - An arguments node. See arguments.py for more details.
    - doc           (Optional[str])
        - The docstring of the function.
    - body          (list[Statement])
        - The list of nodes inside the function.
    - decorators    (Optional[Decorators])
        - The decorators to be applied to this function.
    - returns       (Optional[Name])
        - The return annotation. Only python3 has a return annotation.

Example 1:
    FunctionDef(
        name='fun',
        doc='\n    This is a function fun.\n    ',
        decorators=Decorators(nodes=[Name(name='wrapper')]),
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
        returns=Name(name='str'),
        body=[Assign(
                targets=[AssignName(name='return_annotation')],
                value=Const(value='cool!')),
            Return(value=Name(name='return_annotation'))])


Example 2:
FunctionDef(
    name='no_doc_decor_return_paras_annotation',
    doc=None,
    decorators=None,
    args=Arguments(
        vararg=None,
        kwarg=None,
        args=[],
        defaults=[],
        kwonlyargs=[],
        posonlyargs=[],
        posonlyargs_annotations=[],
        kw_defaults=[],
        annotations=[],
        varargannotation=None,
        kwargannotation=None,
        kwonlyargs_annotations=[],
        type_comment_args=[],
        type_comment_kwonlyargs=[],
        type_comment_posonlyargs=[]),
    returns=None,
    body=[Pass()])
"""


# Example 1
@wrapper
def fun(arg) -> str:
    """
    This is a function fun.
    """
    return_annotation = "cool!"
    return return_annotation


# Example 2
def no_doc_decor_return_paras_annotation():
    pass
