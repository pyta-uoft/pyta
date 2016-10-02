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
    - decorators  (Decorator)
        - The decorator to be applied on this function.
    - returns     (None)
        - The return annotation.

Example:
    - name        -> "fun"
    - args        -> arg
    - doc         -> "This is a function fun."
    - body        -> [Assign(party, "yeah!")]
    - decorators  -> @wrapper
    - returns     -> return party
"""

@wrapper
def fun(arg):
    """
    This is a function fun.
    """
    party = "yeah!"
    return party

