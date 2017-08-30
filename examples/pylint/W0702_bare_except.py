from typing import Optional

def divide(numerator: float, denominator: float) -> Optional[float]:
    """Divide the numerator by the denominator."""
    try:
        return numerator / denominator
    except:
        print("Some exception occurd! Could have been a KeyboardInterrupt!")
