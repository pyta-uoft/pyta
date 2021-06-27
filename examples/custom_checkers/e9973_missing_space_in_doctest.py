"""Examples for E9973 missing-space-in-doctest"""


def f(x: int) -> int:
    """Return one plus x.

    >>>f(10)  # Error on this line: Won't actually be parsed as a doctest!
    11
    """


def f2(x: int) -> int:
    """Return one plus x.

    >>>f(10)  # Error on this line: Won't actually be parsed as a doctest!
    11
    >>>f(11)  # Error on this line: Won't actually be parsed as a doctest!
    12
    """


def f3(x: int) -> int:
    """Return one plus x.

    >>> f(10)
    11
    >>>f(11)  # Error on this line: Won't actually be parsed as a doctest!
    12
    """
