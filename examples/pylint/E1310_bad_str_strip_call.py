"""pylint: bad str strip call
"""
foo = "tests"
foo.lstrip("java")  # Error on this line
