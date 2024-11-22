def print_non_negative_number(x: int):
    """Print number x only if it's greater or equal to 0

    Preconditions:
        - x >= 0
    """
    # the if condition is impossible given the function precondition
    if x < 0:   # Error on this line
        raise Exception("x is smaller than zero")
    print(x)


def impossible_condition(x: bool):
    # the if condition is self-contradictory
    if x and not x:     # Error on this line
        print("impossible")


def spell_number(x: int) -> str:
    """ Spell numbers 0 to 2"""
    if x == 0:
        return "zero"
    elif x == 1:
        return "one"
    elif x == 2:
        return "two"
    elif x == 2:    # this condition is impossible
        return "two again"
