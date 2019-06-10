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
    - func      -> Name(name='ord')
    - args      -> Name(name='c')
    - keywords  -> []

Example 2:
    - func      -> Name(name='func')
    - args      -> [Name(name='a')]
    - keywords  -> [keyword(arg='b', value=Name(id='c'))]

Example 3:
    -func       -> Attribute(expr=Name(name='self'), attrname='method')
    -args       -> Name(name='x')
    -keywords   -> []

Type-checking:
    The type of func must be a function type; the argument types are matched with the parameter types
    of the function. The type of the Call expression itself is equal to the return type of the function.
"""

# Example 1
[ord(c) for line in file for c in line]

# Example 2
func(a, b=c, *d, **e)

# Example 3
self.method(x)
