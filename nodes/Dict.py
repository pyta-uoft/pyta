"""
Dict astroid node

This node represents the Python dictionary objects.

Attributes:
    - items  (List[Tuple[Node, Node]])
        - Contains the tuple of key and value pair, where key and value are
          nodes.

Example:
    - items  -> [[Const(value='b'), Const(value=1)]]


Type-checking:
    Type is Dict[K, V], where K is the most specific class that every key
    of the dictionary is an instance of, and V is the most specific class that
    every value of the dictionary is an instance of.
"""

a = {'b': 1}
