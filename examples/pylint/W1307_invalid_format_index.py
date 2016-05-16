"""pylint: invalid format index.
"""

geopoint = {'latitude':41.123}
point = '{0[latitude]} {0[longitude]}'.format(geopoint) # Error on this line
