"""
Import astroid node

Represents an import statement. Unlike ImportFrom, Import node doesn't have
the attribute "level".

Attributes:
    - names  (List[Tuple])
        - List of tuples of the names of the module that is being imported.

Example 1:
    - names  -> [('astroid', 'ast')]

Example 2:
    - names  -> [('sample_usage.pyta_stats', None)]

Example 3:
    - names  -> [('astroid', None), ('sample_usage', None)]
"""

# Example 1:
import astroid as ast

# Example 2:
import sample_usage.pyta_stats

# Example 3:
import astroid, sample_usage
