"""
FunctionDef astroid node

This node represents a function definition.

Attributes:
    - name        (str)
        - The function's name.
    - args        (Arguments)
        - An arguments node. See Arguments.py for more details.
    - doc         (str)
        - The docstring of the function.
    - body        (List[Statement])
        - The list of nodes inside the function.
    - decorators  (Decorators)
        - The decorators to be applied to this function.
    - returns     (Name)
        - The return annotation. Only python3 has a return annotation.

Example:
    - name        -> "fun"
    - args        -> arg
    - doc         -> "This is a function fun."
    - body        -> [Assign(AssignName(return_annotation)),
                     Return(Name(return_annotation)]
    - decorators  -> [Name(wrapper)]
    - returns     -> str
"""

@wrapper
def fun(arg) -> str:
    """
    This is a function fun.
    """
    return_annotation = "cool!"
    return return_annotation

