"""
Arguments astroid node

The arguments for a function.

Attributes:
    - args         (List[arg])
        - A list of non-keyword argument names.
    - defaults     (List[Node])
        - A list of default values for arguments that can be passed
          positionally.
    - kwonlyargs   (List[arg])
        - A list of keyword-only argument names.
    - kw_defaults  (List[None|arg])
        - A list of default values for keyword-only arguments.
    - vararg       (arg|None)
        - A variable-length argument.
    - kwarg        (arg|None)
        - Single arg nodes and keyword only arguments.

Example:
    - args         -> [arg(arg='a', annotation=Str(s='annotation')),arg(arg='b',
                      annotation=None),arg(arg='c', annotation=None)]
    - defaults     -> [Num(n=1),Num(n=2)]
    - kwonlyargs   -> [arg(arg='e', annotation=None),arg(arg='f',
                      annotation=None)]
    - kw_defaults  -> [None,Num(n=3)]
    - vararg       -> arg(arg='g', annotation=None)
    - kwarg        -> arg(arg='g', annotation=None)
"""

def f(a: 'annotation', b=1, c=2, *d, e, f=3, **g):
    pass
