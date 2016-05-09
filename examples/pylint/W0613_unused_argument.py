"""pylint: Unused argument %r.

"""

def fun(x, y, z):
    return(x + y)

number = fun(1, 2, 3) # Error on this line, 3 is unused.