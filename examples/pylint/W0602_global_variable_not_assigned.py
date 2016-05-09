"""pylint: Using global for %r but no assignment is done.

"""

global var
global var2 # Error on this line

var = 1
print(var) 
