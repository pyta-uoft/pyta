"""pylint: Specify string format arguments as logging function parameters
Used.

"""

import logging

logging.debug("debug logging message %s" % 'one') # Error on this line 
