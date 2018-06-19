"""Examples of unnecessary assignment that the unnecessary assignment checker finds."""


def f():
    x = 17
    y = 40
    z = y + x
    x = 170  # unnecessary assignment here.
    return z


def g():
    q = 17
    r = q + 3
    for i in range(r):
        q += i  # unnecessary assignment here.
    return r


def h():
    s = 7
    z = s**2
    s = "hello 00" + str(7)  # unnecessary assignment here.
    return z


def i():
    z = 1  # unnecessary assignment here.
    z = -1
    return z


def j():
    x = 20
    z = [i for i in range(x)]  # unnecessary assignment here.
    t = 0
    return t

