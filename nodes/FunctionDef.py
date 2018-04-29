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

Type-checking:
    We infer types for the arguments and return type based on the function body;
    the return type is inferred as None if there are no Return nodes in the body.
    This inferred type is unified with any type annotations that appear in the function
    header, and finally this type is used to update the environment in which this function
    declaration appears.
"""

@wrapper
def fun(arg) -> str:
    """
    This is a function fun.
    """
    return_annotation = "cool!"
    return return_annotation

