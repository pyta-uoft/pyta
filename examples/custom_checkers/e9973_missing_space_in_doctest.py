"""Example for E9973 missing-space-in-doctest"""


def f(x: int) -> int:
    """Return one plus x.

    >>>f(10)  # Error on this line: Won't actually be parsed as a doctest!
    11
    """
