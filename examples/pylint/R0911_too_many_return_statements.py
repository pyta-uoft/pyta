"""pylint: too many return statements

Used when a function or method has too many return statement, making it hard to
follow.

Default: 6
"""

def too_many_returns():
    """Example with code that you should not write."""
    thing = 2
    if thing < 10:
        return "Yes"
    elif thing < 9:
        return "No"
    elif thing < 8:
        return "Maybe"
    elif thing < 7:
        return "I don't know"
    elif thing < 6:
        return "..."
    elif thing < 5:
        return "What"

    return "Why"
