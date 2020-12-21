from typing import Any


def is_int_or_str(mystery: Any) -> bool:
    """Return whether mystery is an int or str, or some other type."""
    return isinstance(mystery, int) or isinstance(mystery, str)  # Error on this line
