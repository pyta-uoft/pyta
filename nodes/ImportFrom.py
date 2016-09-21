"""
ImportFrom astroid node

This node represents statement from x import y.

Attributes:
    - modname  (str)
        - The name of the module that is being imported from.
    - names    (List[Alias])
        - List of alias nodes. Each alias node has a name attribute and an
          asname attribute.
    - level    (int)
        - An integer that holds the level of the relative import. 0 means
          absolute import.

Example:
    - module  -> "transforms"
    - names   -> [Alias(TransformVisitor, tfv)]
    - level   -> 0
"""

from transforms import TransformVisitor as tfv
