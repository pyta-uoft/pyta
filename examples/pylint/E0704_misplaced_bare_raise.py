def divide(numerator: float, denominator: float) -> float:
    """Divide two numbers."""
    try:
        return numerator / denominator
    except ZeroDivisionError:
        print("Can't divide by 0...")
    raise  # Error on this line
