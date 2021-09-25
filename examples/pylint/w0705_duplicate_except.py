from typing import Optional

def divide(numerator: float, denominator: float) -> Optional[float]:
    """Divide the numerator by the denominator."""
    try:
        return numerator / denominator
    except ZeroDivisionError:
        print("Can't divide by 0!")
    except ZeroDivisionError:
        print("This duplicate exception block will never be reached!")
