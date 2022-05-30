def add_two_numbers(x=int, y=int) -> int: 
    # type is assigned instead of annotated here, 
    # should be def add_two_numbers(x: int, y: int) -> int
    return x + y


class MyDataType:
    # type is assigned instead of annotated here
    x = int
    y = int