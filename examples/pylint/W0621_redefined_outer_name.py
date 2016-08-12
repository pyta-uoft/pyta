var = None  # var defined here in the outer scope


def fun():
    var = open('/file', 'w')  # redefining var that has already been defined
                              # in the outer scope.
