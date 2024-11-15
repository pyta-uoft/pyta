def return_large_number(x: int) -> int:
    """
    Preconditions
        - x > 1000
    """
    if x > 1000:
        return x


def nested_condition(x: int) -> int:
    if x > 10:
        if x > 5:
            return x
    return 0
