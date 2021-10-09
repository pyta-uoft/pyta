def is_positive(number: int) -> str:
    """Return whether the number is 'positive' or 'negative'."""
    if number > 0: return 'positive'  # Error on this line
    else:
        return 'negative'


def is_negative(number: int) -> bool:
    """Return whether the number is negative."""
    b = number < 0; return b  # Error on this line
