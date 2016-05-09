"""pylint: Truncated. i.e., Logging format string ends in middle of conversion specifier.

"""

import logging

# String truncated on the next line.
logging.basicConfig(format='%(asctime).40s %(message).40s', datefmt='%m/%d/%Y %I:%M:%S %p')
logging.warning('is when this event was logged.')