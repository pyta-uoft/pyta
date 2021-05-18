"""Examples for E9997 forbidden-global-variables."""


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

def add_ex(n: int) -> int:
    """Add ex to n."""
    return ex + n


# The local variable in a comprehension is okay
print({x + 1 for x in [1, 2, 3]})
print({x: x * 3 for x in [1, 2, 3]})
print(list(x + 1 for x in [1, 2, 3]))


def function1() -> int:
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
    return value + 3  # 103


if __name__ == '__main__':
    var1 = 10  # This assignment is okay: statements inside main block are not checked

    if var1 > 5:
        var2 = 13  # This assignment is also okay
