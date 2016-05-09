"""pylint: Too many arguments for logging format string Used
 when a logging format string is given too few arguments.

"""

import logging

# Error on next line.
logging.error('This is a %s %s', 'logging', 'Error', 'Message') 
