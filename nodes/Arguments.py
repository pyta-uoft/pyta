"""
Arguments astroid node

Attributes:
    - args         (list)  list of non-keyword argument names
    - vararg       (arg)   variable-length argument or None
    - kwonlyargs   (list)  list of keyword-only argument names
    - kwarg        (arg)   single arg nodes and keyword only arguments
    - defaults     (list)  n-tuple of the default values of the last n
                           arguments, or None if no default arguments
    - kw_defaults  (list)  list of default values for keyword-only arguments,
                           but if one is None, the corresponding argument is
                           required

Example:
    - args         -> arg
    - vararg       -> None
    - kwonlyargs   -> None
    - kwarg        -> None
    - defaults     -> None
    - kw_defaults  -> None
"""

def fun(arg):
    pass
