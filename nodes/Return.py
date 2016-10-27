"""
Return astroid node

This node represents the Python return statement, which can return any
expression from None to a function Call.

Attributes:
    - value  (Expr)
        - Optionally, the value to be returned, which can be any possible
          expression.

Example 1:
    - value  ->

Example 2:
    - value  -> Num(1)

Example 3:
    - value  -> ListComp(x**2, Comprehension(x, range(10), []))
"""

# Example 1
return

# Example 2
return 1

# Example 3
return [x**2 for x in range(10)]
