def foo(file_path):
    with open(file_path, 'z') as fh:  # Error on this line
        pass
