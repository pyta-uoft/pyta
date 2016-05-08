"""pylint: assignment from none.
"""


def f():
    return None


def g():
    x = f()  # Error on this line
    print(x)
