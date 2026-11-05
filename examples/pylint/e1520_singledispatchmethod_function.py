from functools import singledispatchmethod


@singledispatchmethod  # Error on this line
def describe(value):
    return str(value)
