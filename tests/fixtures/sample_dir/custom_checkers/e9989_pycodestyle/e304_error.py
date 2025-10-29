
def decor(func):
    def inner():
        x = func()
        return 2 * x

    return inner


@decor












def num():
    return 10
