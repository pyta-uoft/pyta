"""pylint: bad format string key
"""

s = 'hello there %(3)s' % {3: 'you'}  # Error on this line
