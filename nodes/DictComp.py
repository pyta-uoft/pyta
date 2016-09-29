"""
DictComp astroid node

A DictComp node represents dictionary comprehensions in Python.

Attributes:
    - key         (node)
        - The part that will be evaluated for each item.
    - value       (node)
        - The part that will be evaluated for each item.
    - generators  (List[Node])
        - A list of comprehension node. See Comprehension node for more details.

Example:
    - key         -> str(n)
    - value       -> n
    - generators  -> [comprehension(for n in range(3))]
"""

{str(n): n for n in range(3)}
