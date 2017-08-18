def function() -> None:
    """A test for the global variables checker."""
    # Change "value" to mean the global variable.
    # (the assignment would be local without "global")
    global VALUE
    VALUE = 100


VALUE = 0
function()
print(VALUE)
ex = 1
print(ex)


def function1() -> None:
    """A test for the global variables checker."""

    def function2() -> None:
        """A test for the global variables checker."""
        # In nested method, reference nonlocal variable
        nonlocal value
        value = 100

    # Set local
    value = 10
    function2()

    # Local variable reflects nonlocal change
    print(value)


if __name__ == '__main__':
    # This assignment is okay
    x = 10

    if x > 5:
        # This assignment is also okay
        y = 13
