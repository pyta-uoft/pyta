"""Example module with a deprecated attribute."""

import configparser

ERROR = configparser.ParsingError("example.ini")
FILENAME = ERROR.filename
