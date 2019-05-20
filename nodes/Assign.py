"""
Assign astroid node

An assignment.

Attributes:
    - targets  (List[Name | Tuple[Name | Starred] | List[Name | Starred]])
        - A list of nodes.
    - value    (Node)
        - A single node.

Example 1:
    - targets  -> [AssignName(id='x')]
    - value    -> Num(n=3)

Example 2:
    - targets  -> [AssignName(id='a'), AssignName(id='b')]
    - value    -> Num(n=1)

Example 3:
    - targets  -> [Tuple(elts=[AssignName(id='a'), AssignName(id='b'),
                   ctx=Store()]
    - value    -> Name(id='c')

Example 4:
    - targets  -> [List(elts=[AssignName(name='a'),
                   Starred(value=AssignName(name='b'), ctx=Store())]
    - value    -> Name(id='d')

Type-checking:
    - Single identifiers are associated with the type of the expression on the RHS of the =.
    - For (unpacking) tuple/list assignment, the RHS must be an iterable of the same length as
      the number of identifiers on the LHS.
      - An exception is when the * operator is used preceding a variable,
        in this case, the remaining values in the iterable will assigned to
        that variable as a list.
"""

# Example 1
x = 3

# Example 2
a = b = 1

# Example 3
a, b = c

# Example 4
[a, *b] = d
