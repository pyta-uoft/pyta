from typing import List
import datetime


class Person:
    name = "Bob"


def add_two_numbers(
    x=int, # Error on this line
    y=List[float], # Error on this line
    z: type = complex # No error on this line
) -> int:
    return (x + y) * z


class MyDataType:
    x = datetime.time # Error on this line
    y = Person # Error on this line
    z: complex = complex # No error on this line
