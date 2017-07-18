var = None  # var defined here in the outer scope


def open_file():
    var = open('/file', 'w')  # redefining name 'var' that has already been
                              # defined in the outer scope.
