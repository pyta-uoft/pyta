"""pylint: unsupported membership test
"""

lst = 1132424
if 'a' in lst:
    print("unsupported membership test")  # Error on this line
