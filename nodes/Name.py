"""
Name astroid node

This node is used to represent variables in Python, storing the name and
contents of the variable. The variable can appear in various contexts, which
are indicated differently in the Name node.

Attributes:
    - id   (Str)
        - The name of the variable.
    - ctx  (class[expr_context])
        - The context in which this variable is used, one of Load, Store or Del.

Example 1:
    - id   -> "my_var"
    - ctx  -> Load

Example 2:
    - id   -> "my_var"
    - ctx  -> Store

Example 3:
    - id   -> "my_var"
    - ctx  -> Del
"""

# Example 1
my_var

# Example 2
my_var = 2

# Example 3
del my_var
