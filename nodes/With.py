"""
With astroid node

This node represents the Python "with" statement, which is used to simplify
set up/tear down actions for a block of code.

Attributes:
    - items  (List[Tuple[Expr]])
        - The expressions or expression-reassigned Name pairs that are to be
          set up by this "with" and torn down after the completion of body.
          Expressions are usually Call or Name nodes.
    - body   (List[Statement])
        - The code to be performed until the with statement closes.

Example:
    - items  -> [Call(open, sys.argv[1]) Name(name='f'),
                 Call(open, 'input.txt') Name(name='i')]
    - body   -> [Pass()]
"""

with open(sys.argv[1]) as f, open('input.txt') as i:
    pass
