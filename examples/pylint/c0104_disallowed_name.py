def is_positive(number: int) -> bool:
    """Check if number is positive."""
    foo = number > 0  # Error on this line: Blacklisted name 'foo'
    return foo
