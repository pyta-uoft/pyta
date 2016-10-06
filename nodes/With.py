"""
With astroid node

This node represents the Python "with" statement, which is used to simplify
set up/tear down actions for a block of code.

Attributes:
    - items  (List[Expr])
        - The expressions or expression-reassigned Name pairs that are to be
          set up by this "with" and torn down after the completion of body.
          Expressions are usually Call or Name nodes.
    - body   (List[Stmt])
        - The code to be performed until the with statement closes.

Example:
    - items  -> Call(open, sys.argv[1]) Name('f', Load())
    - body   -> [Node(Pass)]
"""

with open(sys.argv[1]) as f:
    pass
