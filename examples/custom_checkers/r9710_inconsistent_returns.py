import math
from typing import Optional


def add_sqrts(x: float, y: float) -> Optional[float]:
    """Return the sum of the square roots of x and y, or None if
    either number is negative."""
    if x >= 0 and y >= 0:
        return math.sqrt(x) + math.sqrt(y)
    else:
        return  # Error: this should be `return None` instead.


def str_to_int(s: str) -> Optional[int]:
    """Return the integer representation of the string s, or None if it cannot be converted."""
    try:
        return int(s)
    except ValueError:
        return  # Error: this should be `return None` instead.


if __name__ == "__main__":
    import python_ta
    python_ta.check_all()
