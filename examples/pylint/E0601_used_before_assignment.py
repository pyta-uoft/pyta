"""pylint: Using variable %r before assignment Used when
a local variable is accessed before it’s assignment.

"""

print(a) # Error on this line
a = 1