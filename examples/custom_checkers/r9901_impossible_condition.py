def print_natural_number(x: int):
    """
    Preconditions:
        - x >= 0
    """
    if x < 0:
        raise Exception("x is not an integer")
    print(x)


def invalid_condition(x: bool):
    if x and not x:
        print("impossible")
