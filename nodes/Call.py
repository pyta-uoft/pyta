"""
Call astroid node

A function call.

Attributes:
    - func      (Name | Attribute)
        - The function.
    - args      (List[args])
        - List of the arguments passed by position.
    - keywords  (List[keyword])
        - List of keyword objects representing arguments passed by keyword.

Example 1:
    - func      -> print
    - args      -> []
    - keywords  -> [1]

Example 2:
    - func      -> print
    - args      -> [x == 4]
    - keywords  -> ['x is indeed 4']
"""

# Example 1
print(1)

# Example 2
if x == 4:
    print('x is indeed 4')
