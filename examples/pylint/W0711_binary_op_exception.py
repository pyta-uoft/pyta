def divide_and_square(numerator: float, denominator: float) -> float:
    """Divide the numerator by the denominator and square the result."""
    try:
        return (numerator / denominator) ** 2
    except ZeroDivisionError or OverflowError:  # Error on this line
        return float('nan')
