def add_one(num: int) -> int:
    """Return num increased by one."""
    return num + 1


(lambda x: add_one(x))(1)  # Error on this line
