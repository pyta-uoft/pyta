file_data = None  # 'file_data' defined here in the outer scope

def read_file(filename) -> str:
    """Read the contents of a file."""
    with open(filename) as fh:
        file_data = fh.read()  # Redefining name 'file_data' that has already been
    return file_data           # defined in the outer scope.
