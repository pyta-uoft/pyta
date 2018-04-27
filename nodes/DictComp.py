"""
DictComp astroid node

A DictComp node represents dictionary comprehensions in Python.

Attributes:
    - key         (Node)
        - The key that will be evaluated for each value.
    - value       (Node)
        - The value that will be evaluated for each iteration.
    - generators  (List[Comprehension])
        - A list of comprehension node. See Comprehension node for more details.
    - locals      (Dict)
        - Contains the variables in the local scope.

Example:
    - key         -> str(n)
    - value       -> n
    - generators  -> [Comprehension(n, range(3))]
    - locals      -> {'key': str(n), 'value': n,
                     'generators': (for n in range(3))}

Type-checking:
    The type of the DictComp is Dict[K, V], where K is the type of key and V is the type of value.
"""

{str(n): n for n in range(3)}
