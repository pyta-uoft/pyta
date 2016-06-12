def no_catching():
    try:
        raise TypeError()
    except:
        print('Requires an exception class')
