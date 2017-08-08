var = None  # var defined here in the outer scope

def open_file() -> None:
    var = open('/file', 'w')  # Redefining name 'var' that has already been
                              # defined in the outer scope.
