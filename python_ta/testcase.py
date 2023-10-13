def some_function():
    x = 5  # pylint:
    y = 0
    result = x / y
    return result


a = 10
b = 20
if __name__ == "__main__":
    import python_ta

    options = {"allow-pylint-comments": False}
    python_ta.check_all()
