class MyException(Exception):
    pass


class MyDoubleException(Exception):
    pass


def binary_capture():
    try:
        # Not caught, 'or' doesn't do what you think.
        # Need to do: except (MyException, MyDoubleException):
        raise MyDoubleException()
    except MyException or MyDoubleException:
            print('Will not detect MyDoubleException due to how "or" works')
