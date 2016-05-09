"""pylint: bad str strip call
"""

string = "tests"
string.lstrip("java")  # Error on this line
