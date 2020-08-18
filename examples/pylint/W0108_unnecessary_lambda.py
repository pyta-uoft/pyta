def add_one(num: int) -> int:
    """Calculate the sum of the elements in the given list."""
    return num + 1


(lambda x: add_one(x))(1)  # Error on this line
