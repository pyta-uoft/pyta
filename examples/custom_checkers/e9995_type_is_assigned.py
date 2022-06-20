from typing import List, Dict

def add_two_numbers(x=int, y=List[float], z: type = complex) -> int: 
    # type is assigned instead of annotated here, 
    # should be def add_two_numbers(x: int, y: int) -> int
    return (x + y) * z


class MyDataType:
    # type is assigned instead of annotated here
    x = bool
    y = Dict[str, str]
    # checker should not pick this up
    z: complex = complex