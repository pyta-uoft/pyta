"""
Comprehension astroid node

Constructs that allow sequences to be built from other sequences.

Attributes:
    - target  (Node)
        - Typically a name or tuple node; the reference to use for each element.
    - iter    (Node)
        - The object to iterate over.
    - ifs     (List[Expr])
        - List of test expressions. If None, ifs is an empty list.

Example:
    * NOTE : The example below is of a Comprehension Node "for x in range(3)" within
             a ListComprehension Node "[x for x in range(3)]".
             
    - target  -> Name(id='line', ctx=Store())
    - iter    -> Name(id='range(3)', ctx=Load())
    - ifs     -> []

Type-checking:
    Unify the target against the "contained" type in the iterable.
"""

[x for x in range(3)]
