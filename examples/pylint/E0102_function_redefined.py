def positive(obj: int) -> bool:
    return obj > 0


def positive(obj: int) -> bool:  # Error on this line: Function redefined
    return obj >= 0
