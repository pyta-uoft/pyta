"""pylint: simplifiable if statement

"""

def is_even(num):
    """Return whether <num> is even or odd."""
    if num % 2 == 0:
        return True
    else:
        return False
