"""
Call astroid node

A function call.

Attributes:
    - args      (Optional[list[NodeNG]])
        - List of the arguments passed by position.
    - func      (Optional[Name | Attribute])
        - The function being called.
    - keywords  (Optional[list[NodeNG]])
        - List of keyword objects representing arguments passed by keyword.
          If None, keywords is an empty list.
    - kwargs    (list[Keyword])
        - The keyword arguments that unpack something.
    - starargs  (list[Starred])
        - The positional arguments that unpack something.

Example 1:
    Call(
        func=Name(name='ord'),
        args=[Name(name='c')],
        keywords=None)

Example 2:
    Call(
        func=Name(name='func'),
        args=[
            Name(name='a'),
            Starred(
                ctx=<Context.Load: 1>,
                value=Name(name='d'))],
        keywords=[
            Keyword(
                arg='b',
                value=Name(name='c')),
                Keyword(
                    arg=None,
                    value=Name(name='e'))])


Example 3:
    Call(
        func=Attribute(
            attrname='method',
            expr=Name(name='self')),
        args=[Name(name='x')],
        keywords=None)

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
