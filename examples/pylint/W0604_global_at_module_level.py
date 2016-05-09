"""pylint: Using the global statement at the module level has no effect.

"""

def some_fun(var):
    var += 1
    print(var)

global var # Global statement at the module level.
var = 3
some_fun(var)