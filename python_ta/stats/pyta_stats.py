# Use os.walk to walk through all the files in a directory from top to bottem.
# Everytime when os.walk walks a file, check if the file is a python file, if
# it is, then run a check_all on it.
# os.walk doesn't return anything


def pyta_statistics(directory):
    """
    Recursively run python_ta.check_all() on the files in directory to the files
    in its subdirectories. Record the number of occurrences of each type of
    errors in a dictionary.

    @param str directory: The string of the path way of the directory.
    @rtype: None
    """
    pass


def frequent_errors(error_dict):
    """
    Sort the errors in error_dict from the most frequent to least frequent in a
    list

    @type error_dict: Dict
    @rtype: list
    """
    # Stored in a list so easier to report the top or top three or top five most
    # frequently occurred error.
    pass
