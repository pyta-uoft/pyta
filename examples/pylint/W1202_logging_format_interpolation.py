"""pylint: Use % formatting in logging functions and pass the % parameters as arguments.

"""

import logging

logging.debug('logging: {}'.format('message')) # Error on this line