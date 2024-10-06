"""Example for C9960 unmentioned-parameter"""


def multiply(a: int, b: int) -> int:  # C9960: 'a' and 'b' are not mentioned
    """Multiply two numbers."""
    return a * b


def divide(numerator: int, denominator: int) -> float:  # C9960: 'denominator' is not mentioned
    """Divide the numerator by the denominator.

    Parameters:
    numerator: The number to be divided.
    """
    return numerator / denominator


def generate_list(n: int) -> list:  # C9960: 'n' is not mentioned in the main docstring (only in doctests)
    """Generate a list of numbers

    >>> n = 3
    >>> generate_list(n)
    [0, 1, 2]
    """
    return [i for i in range(n)]
