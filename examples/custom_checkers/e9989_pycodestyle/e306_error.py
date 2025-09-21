def outer():
    x = 'hello'
    def inner():  # expected line before nested function
        return 'world'
    return x + inner()
