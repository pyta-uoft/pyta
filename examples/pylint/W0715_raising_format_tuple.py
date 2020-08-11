class DivisionException(Exception):
    def __init__(self, message: str, numerator: int, denominator : int):
        self.message = message
        self.numerator = numerator
        self.wasZeroDivide = (denominator == 0)
        super().__init__()


def divide(numerator: int, denominator: int) -> float:
    """Divide the numerator by the denominator."""
    try:
        return numerator / denominator
    # Error on the following line, in particular the first argument
    except DivisionException("You can't do {n} / % {d}", numerator, denominator):
        raise