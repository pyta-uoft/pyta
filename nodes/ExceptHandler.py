"""
ExceptHandler astroid node

ExceptHandler is a single except clause.

Attributes:
    - type  (node)
        - Typically a Name node like ValueError or TypeError.
    - name  (str)
        - A raw string for the name to hold the exception.
    - body  (List[Node])
        - A list of nodes.

Example 1:
    - type  -> None
    - name  -> None
    - body  -> [pass]

Example 2:
    - type  -> ValueError
    - name  -> None
    - body  -> [print("NOOOOOO!!!!!!!!!")]
"""

#Example 1
try:
    pass
except:
    pass

#Example 2
try:
    x = int(input("Please enter a number"))
except ValueError:
    print("NOOOOOO!!!!!!!!!")
