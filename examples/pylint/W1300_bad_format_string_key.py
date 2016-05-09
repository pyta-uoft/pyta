"""pylint: bad format string key
"""

print('hello there %(3)s' % {3: 'you', '3': 'you'})  # Error on this line
