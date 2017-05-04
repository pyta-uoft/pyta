"""
Expr astroid node

When an expression, such as a function call, appears as a statement by itself
with its return value not used or stored, it is wrapped in Expr node.

Attributes:
    - value  (Node)
        - Value holds nodes like Name, Lambda, Yield or YieldFrom.

Example:
    - value  -> print(1)
"""

print(1)
(100 * 42)
101 * 43

# Extra examples
0
6.0
"a"
(1,2)
True
None
[1,2,3]
{"a":1,"b":2}
"a"[0]
(1,2)[0]
[1,2,3][0]
{"a":0,"b":1}[0]
