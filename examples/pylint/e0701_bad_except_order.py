from typing import Optional

def divide(numerator: float, denominator: float) -> Optional[float]:
    """Divide the numerator by the denominator."""
    try:
        return numerator / denominator
    except Exception:
        print("Some exception occurd! But I don't know which one?!")
    except ZeroDivisionError:
        print("This exception block will never be reached!")
