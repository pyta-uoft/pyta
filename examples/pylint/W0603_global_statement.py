"""pylint: Just trying to discourage the global usage!

"""

def fun():
    global var # Globel Statement
    var = "I'm a variable"
    print(var)

fun() 
