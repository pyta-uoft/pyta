def error_code(error_codes):

    try:
        print(error_codes[0])
    except IndexError:
        return error_codes[1]
    finally:
        return error_codes[2]  # Error on this line
