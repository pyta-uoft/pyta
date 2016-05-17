"""pylint: Redefining name %r from outer scope (line %s) Used
when a variable’s name has been defined in the outer scope.

"""

var = None

def fun():
    var = open('/file', 'w') # Error on this line 
