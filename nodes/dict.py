"""
Dict astroid node

This node represents the Python dictionary objects.

Attributes:
    - items (list[tuple[NodeNG, NodeNG]])
        - Contains a list of key-value-pair tuples, where key and value are
          nodes.

Example 1:
    Dict(items=[[Const(value='b'), Const(value=1)]])

Example 2:
    Dict(items=[[Name(name='my_key'), Name(name='my_value')],
        [BinOp(
            op='+',
            left=Const(value=3),
            right=Const(value=2)),
        Subscript(
            ctx=<Context.Load: 1>,
            value=Name(name='x'),
            slice=Const(value=0))]])

Representation tree of Dict nodes show each KVP as a list;
however, the actual .items attribute stores each KVP as a tuple.

Type-checking:
    Type is dict[K, V], where K is the most specific class that every key
    of the dictionary is an instance of, and V is the most specific class that
    every value of the dictionary is an instance of.
"""

# Example 1
{'b': 1}

# Example 2
{my_key: my_value, 3 + 2: x[0]}
