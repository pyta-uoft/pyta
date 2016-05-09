"""pylint: Unsupported logging format character %r (%#02x) at index %d.

"""

import logging

# Error on next line.
logging.error('Logging%20Error Message %s', 'One') 
