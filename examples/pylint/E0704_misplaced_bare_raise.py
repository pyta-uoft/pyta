def func() -> None:
    try:
        raise MyException()
    except MyException:
        # Do something important here (if needed).
        # Now, raise again what we just caught.
        raise
