def func(num: float) -> None:
    try:
        raise ZeroDivisionError()
    except Exception:
        print('This is always triggered')
    except ZeroDivisionError:
        print('Cannot ever be reached')
