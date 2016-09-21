"""
ListComp astroid node

Attributes:
    - elt         (node)  The part to be evaluated to make every item
                          in the list.
    - generators  (list)  The list of comprehension nodes representing every
                          "for" clause in the list comprehension.

Example:
    - elt         -> l+l
    - generators  -> [comprehension(l, 'str', [])]
"""

[l+l for l in 'str']
