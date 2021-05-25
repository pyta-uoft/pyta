try:
    print(x)
except NameError as OSError:  # Error on this line: exception assigned to an existing name
    print(OSError)
