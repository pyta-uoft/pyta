"""
Call astroid node

A function call.

Attributes:
    - func      (Name | Attribute)
        - The function.
    - args      (List[Node])
        - List of the arguments passed by position.
    - keywords  (List[Keyword])
        - List of keyword objects representing arguments passed by keyword.

Example 1:
    - func      -> print
    - args      -> []
    - keywords  -> [1]

Example 2:
    - func      -> Name(id='func', ctx=Load())
    - args      -> [Name(id='a', ctx=Load())]
    - keywords  -> [keyword(arg='b', value=Name(id='c', ctx=Load()))]
"""

# Example 1
print(1)

# Example 2
def func(a, b=c, *d, **e):
    pass
