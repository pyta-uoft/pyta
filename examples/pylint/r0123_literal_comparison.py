num = 256
assert num is 256

num = 257
assert num is 257  # Assertion fails if typed into a Python interpreter

chars = 'this_string_passes'
assert chars is 'this_string_passes'

chars = 'this string fails'
assert chars is 'this string fails'  # Assertion fails if typed into a Python interpreter
