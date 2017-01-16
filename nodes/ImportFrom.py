"""
ImportFrom astroid node

This node represents statement from x import y.

Attributes:
    - modname  (str)
        - The name of the module that is being imported from.
    - names    (List[Tuple])
        - List of tuples of the names of the functions that are being imported.
    - level    (int | NoneType)
        - An integer that holds the level of the relative import. 0 means
          absolute import.

Example 1:
    - modname  -> "transforms"
    - names    -> [("TransformVisitor", "tfv")]
    - level    -> None

Example 2:
    - modname  -> "sample_usage.pyta_stats"
    - names    -> [("pyta_statistics", None), ("_print_stats", None)]
    - level    -> None

Example 3:
    - modname  -> ""
    - names    -> [("level_is_2", "l2")]
    - level    -> 2

Example 4:
    - modname  -> ""
    - names    -> [("level_is_3", "l3")]
    - level    -> 3
"""

# Example 1:
from transforms import TransformVisitor as tfv

# Example 2:
from sample_usage.pyta_stats import pyta_statistics, _print_stats

# Example 3:
from .. import level_is_2 as l2

# Example 4:
from ... import level_is_3 as l3
