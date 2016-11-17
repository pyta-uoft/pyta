"""
FunctionDef astroid node

A function definition.

Attributes:
    - name        (str)
        - The function's name.
    - args        (Arguments)
        - An arguments node. See Arguments.py for more details.
    - doc         (str)
        - The docstring of the function.
    - body        (List[Node])
        - The list of nodes inside the function.
    - decorators  (List[Decorators])
        - The list of decorators to be applied to this function.
    - returns     (None)
        - The return annotation. Only python3 has a return annotation.

Example:
    - name        -> "fun"
    - args        -> arg
    - doc         -> "This is a function fun."
    - body        -> [Assign(return_annotation, "cool!")]
    - decorators  -> [@wrapper]
    - returns     -> str
"""

@wrapper
def fun(arg) -> str:
    """
    This is a function fun.
    """
    return_annotation = "cool!"
    return return_annotation

