"""Example for C9960 unmentioned-parameter"""


def multiply(a: int, b: int) -> int:
    """Multiply two numbers."""  # C9960: 'a' and 'b' are not mentioned
    return a * b


def divide(numerator: int, denominator: int) -> float:
    """
    Divide the numerator by the denominator.

    Parameters:
    numerator: The number to be divided.
    """  # C9960: 'denominator' is not mentioned
    return numerator / denominator


def generate_list(n: int) -> list:
    """
    Generate a list of numbers

    >>> generate_list(3)
    [n for n in range(3)]
    >>> generate_list(5)
    [n for n in range(5)]
    """  # C9960: 'n' is not mentioned in the main docstring (only in doctests)
    return [i for i in range(n)]
