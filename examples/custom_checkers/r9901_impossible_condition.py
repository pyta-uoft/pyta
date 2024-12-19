def print_none_negative_number(x: int) -> None:
    """Print number x only if it's greater or equal to 0

    Preconditions:
        - x >= 0
    """
    # the if condition is impossible given the function precondition
    if x < 0:   # Error on this line
        raise Exception("x is smaller than zero")
    print(x)


def impossible_condition(x: bool) -> None:
    # the if condition is always false
    if x and not x:     # Error on this line
        print("impossible")


def display_number(x: int) -> str:
    """Display numbers 0 to 2 in word"""
    if x == 0:
        "zero"
    elif x == 1:
        return "one"
    elif x == 2:
        return "two"
    elif x == 2:    # Error on this line
        return "two again"
