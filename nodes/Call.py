"""
Call astroid node

A function call.

Attributes:
    - func      (Name | Attribute)
        - The function.
    - args      (List[Node])
        - List of the arguments passed by position.
    - keywords  (List[Keyword] | None)
        - List of keyword objects representing arguments passed by keyword.
          If None, keywords is an empty list.

Example 1:
    - func      -> Name(id='print', ctx=Load())
    - args      -> Name(id='ord', ctx=Load())
    - keywords  -> []

Example 2:
    - func      -> Name(id='func', ctx=Load())
    - args      -> [Name(id='a', ctx=Load())]
    - keywords  -> [keyword(arg='b', value=Name(id='c', ctx=Load()))]
"""

# Example 1
[ord(c) for line in file for c in line]

# Example 2
func(a, b=c, *d, **e)
