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


# The local variable in a comprehension is okay
print([x for x in [1, 2, 3]])
print({x + 1 for x in [1, 2, 3]})
print({x: x * 3 for x in [1, 2, 3]})
print(list(x + 1 for x in [1, 2, 3]))


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
    value + 3  # 103


if __name__ == '__main__':
    # This assignment is okay
    x = 10

    if x > 5:
        # This assignment is also okay
        y = 13
