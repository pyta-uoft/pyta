from typing import Union

def is_int(obj: Union[int, float, str]) -> bool:
    """Check if the given object is of type 'int'."""
    return type(obj) == int  # Error on this line
