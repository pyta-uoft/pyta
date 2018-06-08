x = 0


def f(a):
    return a + x


def g(b):
    return b + 'abc'


g(f(x))
