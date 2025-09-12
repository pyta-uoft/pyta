def outer():
    x = 'hello'
    def inner():
        return 'world'
    return x + inner()
