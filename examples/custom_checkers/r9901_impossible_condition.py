def print_non_negative_number(x: int) -> None:
    """Print the non-negative number x.

    Preconditions:
        - x >= 0
    """
    if x < 0:  # Error on this line
        raise ValueError("x is negative")
    print(x)


def print_if_true(value: bool) -> None:
    """Print a message when value is true."""
    if value and not value:  # Error on this line
        print("value is true")


def display_number(x: int) -> str:
    """Return the word for x, or 'other' when x is outside the range 0 to 2."""
    if x == 0:
        return "zero"
    elif x == 1:
        return "one"
    elif x == 2:
        return "two"
    elif x == 2:  # Error on this line
        return "two again"
    else:
        return "other"
