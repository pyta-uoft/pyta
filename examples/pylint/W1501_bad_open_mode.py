"""pylint: bad open mode

Python supports: r, w, a[, x] modes with b, +, and U (only with r) options.
"""

def exists(filename):
    """Example that opens a file"""
    try:
        file = open(filename, 'rw')  # For example, "rw" is not a valid mode.
        file.close()
        return True
    except IOError:
        # Example only.
        pass
