"""Python script used for testing that the correct number of error occurrences are being displayed."""

# The following imports are used solely to trigger error messages.
import packaging
import pip
import pygments
import pylint


def sum_items(lst: list[int]) -> int:
    """..."""
    s = 0
    for i in range(len(lst)):
        s += lst[i]
    return s


def sum_items2(lst: list[int]) -> int:
    """..."""
    s = 0
    for i in range(0, len(lst)):
        s += lst[i]
    return s


def sum_items3(lst: list[int]) -> int:
    """..."""
    s = 0
    for i in range(0, len(lst), 1):
        s += lst[i]
    return s
