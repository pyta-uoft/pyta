"""pylint: assignment from no return.
"""


def f():
    print("s")


def g():
    x = f()  # Error on this line
    print(x)
