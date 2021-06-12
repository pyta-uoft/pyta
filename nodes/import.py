"""
Import astroid node

Represents an import statement. Unlike ImportFrom, Import node doesn't have
the attribute "level".

Attributes:
    - names (list[tuple[str, Optional[str]]])
        - List of tuples containing the name of the module and its assigned alias (if applicable)

Example 1:
    Import(names=[['astroid', 'ast']])

Example 2:
    Import(names=[['sample_usage.pyta_stats', None]])

Example 3:
    Import(names=[['astroid', None], ['sample_usage', None]])

The representation trees display the pair of module name and its alias as a list, when the actual
data type is a tuple.
"""

# Example 1:
import astroid as ast

# Example 2:
import sample_usage.pyta_stats

# Example 3:
import astroid, sample_usage
