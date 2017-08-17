def no_catching() -> None:
    try:
        raise TypeError()
    except:
        print('Requires an exception class')
