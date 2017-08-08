from typing import Optional

def square(number: float) -> Optional[float]:
    if number == None:  # Error on this line
        return None
    return number**2
