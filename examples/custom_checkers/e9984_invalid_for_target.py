"""Examples for E9984: invalid-for-target."""


def example1(lst: list[int]) -> int:
    """For loop target is an element of a list."""
    s = 0
    for lst[0] in lst:  # Error on this line. lst[0] is highlighted.
        s += lst[0]
    return s


def example2(lst: list[int]) -> list[int]:
    """For loop target is a slice of a list."""
    s = []
    for lst[0:1] in lst:  # Error on this line. lst[0:1] is highlighted.
        s += lst[0:1]
    return s


def example3(lst: list[int]) -> int:
    """For loop target is an object's attribute"""
    x = type("EmptyClass", (), {})
    s = 0
    for x.attr in lst:  # Error on this line. x.attr is highlighted
        s += x.attr
    return s


def example4(lst: list[tuple[int, int]]) -> int:
    """There are more than one for loop targets."""
    s = 0
    for lst[0], i in lst:  # Error on this line. lst[0] is highlighted.
        s += lst[0] * i
    return s


def example5(lst: list[tuple[int, int]]) -> int:
    """Multiple for loop targets are in a list"""
    s = 0
    for [lst[0], i] in lst:  # Error on this line. lst[0] is highlighted.
        s += lst[0] * i
    return s


def example6(lst: list[tuple[int, tuple[int, int]]]) -> int:
    """For loop targets nested in lists or tuples"""
    s = 0
    for i, [j, lst[0]] in lst:  # Error on this line. lst[0] is highlighted.
        s += i * j * lst[0]
    return s
