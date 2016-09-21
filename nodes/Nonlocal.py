"""
Nonlocal astroid node

Attributes:
    - names  (list)  The list of strings of the names of variables to be
                     rebound as nonlocal.

Example:
    - names  -> ['x']
"""

x = 1
def inner():
    nonlocal x
