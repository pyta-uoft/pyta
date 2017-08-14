from typing import Optional

def square(number: Optional[float]) -> Optional[float]:
    if number == None:  # Error on this line
        return None
    else:
        return number**2
