"""This file illustrates basic usage of PythonTA's code analysis.
"""


def add_two(x: int, y: int) -> int:
    """Return the sum of x and y.

    PythonTA's analysis of this code will report three issues:

    1. A missing return statement (a logical error)
    2. Missing whitespace around the + (a formatting issue)
    3. The presence of a print call (a code style issue)
    """
    result = x + y
    print(result)


if __name__ == "__main__":
    import python_ta

    python_ta.check_all()
