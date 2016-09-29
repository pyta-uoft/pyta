"""
ImportFrom astroid node

This node represents statement from x import y.

Attributes:
    - module  (str)
        - The name of the module that is being imported from.
    - names   (Node)
        - List of alias nodes. Each alias node has a name attribute and an
          asname attribute.
    - level   (int)
        - An integer that holds the level of the relative import. 0 means
          absolute import.

Example:
    - module  -> "transforms"
    - names   -> [alias(TransformVisitor)]
    - level   -> 1
"""

from astroid.transforms import TransformVisitor
