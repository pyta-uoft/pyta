"""
Comprehension astroid node

Attributes:
    - target  (class)  typically a name or tuple node; the reference to use for
                       each element
    - iter    (node)   the object to iterate over
    - ifs     (list)   list of test expressions

Example:
    - target  -> x
    - iter    -> range(3)
    - ifs     -> []
"""

[x for x in range(3)]
