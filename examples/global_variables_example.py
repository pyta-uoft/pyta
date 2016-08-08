def function():
    """ A test for the global variables checker
    @rtype: None
    """
    # Change "value" to mean the global variable.
    # ... The assignment will be local without "global."
    global VALUE
    VALUE = 100

VALUE = 0
function()
print(VALUE)
ex = 1
print(ex)


def function1():
    """ A test for the global variables checker
    @rtype: None
    """

    def function2():
        """ A test for the global variables checker
         @rtype: None
        """
        # In nested method, reference nonlocal variable.
        nonlocal value
        value = 100

    # Set local.
    value = 10
    function2()

    # Local variable reflects nonlocal change.
    print(value)


if __name__ == '__main__':
    # This assignment is okay
    x = 10
