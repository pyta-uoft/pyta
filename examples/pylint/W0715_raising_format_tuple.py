class DivisionException(Exception):
    def __init__(self, message: str, numerator: int, denominator : int):
        self.message = message
        self.numerator = numerator
        self.wasZeroDivide = (denominator == 0)
        super().__init__()


def divide(numerator: int, denominator: int) -> float:
    """Divide the numerator by the denominator."""
    if denominator == 0:
        raise DivisionException("You can't do {n} / % {d}", numerator, denominator)
    else:
        return numerator / denominator
