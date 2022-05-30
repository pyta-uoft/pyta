import python_ta

python_ta.check_all("test.py")


def add_two_numbers(x=int, y=int) -> int:
    # type is assigned instead of annotated here,
    # should be def add_two_numbers(x: int, y: int) -> int
    return x + y
