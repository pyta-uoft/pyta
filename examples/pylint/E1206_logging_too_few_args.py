"""pylint: Not enough arguments for logging format string Used
 when a logging format string is given too many arguments.

"""

import logging

# Error on next line.
logging.error('This is an %s %s %s', 'Error', 'Message')