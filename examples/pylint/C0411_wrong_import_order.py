"""pylint: wrong import order

Used when PEP8 import order is not respected (standard imports first,
then third-party libraries, then local imports)
"""

import your_own_module  # your own modules should be imported last.
import sys  # "standard modules" should be imported first
