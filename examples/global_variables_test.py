"""Test file for global variables checker
"""


def method():
    """ A test for the global variables checker
    @rtype: None
    """
    # Change "value" to mean the global variable.
    # ... The assignment will be local without "global."
    global VALUE
    VALUE = 100

VALUE = 0
method()
print(VALUE)


def method1():
    """ A test for the global variables checker
    @rtype: None
    """

    def method2():
        """ A test for the global variables checker
         @rtype: None
        """
        # In nested method, reference nonlocal variable.
        nonlocal value
        value = 100

    # Set local.
    value = 10
    method2()

    # Local variable reflects nonlocal change.
    print(value)
