
def decor(func):
    """Decorator that multiplies by 2"""
    def inner():
        x = func()
        return 2 * x

    return inner


@decor

def num():
    """Returns 10"""
    return 10
