def is_positive(number: int) -> bool:
    """Check if number is positive."""
    return number > 0


def is_positive(number: int) -> bool:  # Error on this line: Function redefined
    """Check if number is positive."""
    return number >= 0
