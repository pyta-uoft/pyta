"""pylint: Global variable %r undefined at the module level. i.e., defined
through the "global" statement but not defined in the module scope.

"""

def fun():
    """Using global variable keyword"""

    global var  # Defined locally, it becomes global.
    var = 1 # initialize locally