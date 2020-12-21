from typing import Any


def f(x: Any) -> bool:
    """Return whether x is one of a few different values."""
    return x == 1 or x == "hello" or x == 2.5  # Error on this line
