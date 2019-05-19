def outer():
    x = y = 1
    def inner():
        nonlocal x, y
        x += y
    inner()
