"""
DictComp astroid node

Attributes:
    - key         (node)  the part that will be evaluated for each item
    - value       (node)  the part that will be evaluated for each item
    - generators  (list)  a list of comprehension node

Example:
    - key         -> str(n)
    - value       -> n
    - generators  -> for n in range(3)
"""

{str(n): n for n in range(3)}
