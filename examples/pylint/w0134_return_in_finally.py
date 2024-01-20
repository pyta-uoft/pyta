def error_code():

    error_codes = [0, 1, 2]

    try:
        return error_codes[2]
    except IndexError:
        return error_codes[1]
    finally:
        return error_codes[0]  # Error on this line
