def print_natural_number(x: int):
    """
    Preconditions:
        - x >= 0
    """
    if x < 0:
        raise Exception("x is not a natural number")
    print(x)


def invalid_condition(x: bool):
    if x and not x:
        print("impossible")


def spell_number(x: int) -> str:
    if x == 0:
        return "zero"
    elif x == 1:
        return "one"
    elif x == 2:
        return "two"
    elif x == 2:    # this condition is impossible
        return "two again"
