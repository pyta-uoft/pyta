"""Broad Exception Caught Example"""
# The caught exception below is too broad and vague.
try:
    1 / 0
except Exception:  # Error on this line
    print('An error occurred')
