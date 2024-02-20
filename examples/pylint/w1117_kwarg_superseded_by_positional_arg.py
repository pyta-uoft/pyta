"""Examples for W1117: kwarg-superseded-by-positional-arg"""


def print_greeting(greeting="Hello", /, **kwds) -> None:
    """Prints out the greeting provided as a positional argument,
    or "Hello" otherwise.
    """
    print(greeting)


print_greeting(greeting="Hi")  # Error on this line
