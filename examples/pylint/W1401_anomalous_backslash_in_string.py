"""pylint: anomalous backslash in string
"""
import re
re.compile("\d{3}")  # Error on this line
