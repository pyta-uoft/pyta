from __future__ import annotations

def set_values() -> tuple[int, int]:
    """Return a tuple of two integers."""
    var1 = 1
    var2 = 2
    return var1, var2

# Error on the following line. Cannot unpack 2 items into 3 variables.
one, two, three = set_values()
