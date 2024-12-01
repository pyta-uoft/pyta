def return_large_number(x: int) -> int:
    """Return number x only if it's greater than 1000

    Preconditions:
        - x > 1000
    """
    # the if condition is already checked by function precondition
    if x > 1000:   # Error on this line
        return x


def nested_condition(x: int) -> int:
    if x > 10:
        # the condition `x > 5` is already guaranteed by `x > 10`
        if x > 5:   # Error on this line
            return x
    return 0


def redundant_condition(x: bool):
    # the if condition is always true
    if x or not x:     # Error on this line
        print("redundant")
