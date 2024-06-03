def hello() -> None:
    """Print a message to the user."""
    # You should not use input action in some assignments
    name = input("What is your name?")  # Error on this line

    # You should not use print action in some assignments
    print('hello, ' + name)  # Error on this line


if __name__ == '__main__':
    hello()
