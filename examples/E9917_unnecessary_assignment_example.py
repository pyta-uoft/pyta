"""Examples of unnecessary assignment that the unnecessary assignment checker finds."""


def f():
    """
    Unnecessary assignment after use of variable.
    """
    x = 17
    y = 40
    z = y + x
    x = 170  # unnecessary assignment here.
    return z


def g():
    """
    Unnecessary augmented assignment.
    """
    q = 17
    r = q + 3
    for i in range(r):
        q += i  # unnecessary assignment here.
    return r


def h():
    """
    Unnecessary assignment of variable before use of variable.
    """
    z = 1  # unnecessary assignment here.
    z = -1
    return z


def m():
    """
    Unnecessary assignment because variable n is unused.
    """
    n = 17  # unnecessary assignment here.
    return 17


def n():
    """
    Unnecessary assignment because all paths reassign variable.
    """
    b = True
    c = 4  # Unnecessary assignment here.
    if b:
        c = 8
    else:
        c = 2
    return c
