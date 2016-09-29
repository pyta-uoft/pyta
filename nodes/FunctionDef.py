"""
FunctionDef astroid node

A function definition.

Attributes:
    - name            (str)
        - The function's name.
    - args            (Node)
        - An arguments node. See Arguments.py for more details.
    - body            (list)
        - The list of nodes inside the function.
    - decorator list  (List[Decorator])
        - See Decorators.py for more details.
    - returns         (None)
        - The return annotation.

Example:
    - name            -> "fun"
    - args            -> arg
    - body            -> [pass]
    - decorator list  -> [@wrapper]
    - returns         -> None
"""

@wrapper
def fun(arg):
    pass
