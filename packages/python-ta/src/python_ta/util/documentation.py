"""Helpers for linking to PythonTA documentation."""

HELP_URL = "https://www.cs.toronto.edu/~david/pyta/checkers/index.html"


def get_documentation_url(msg_id: str) -> str:
    """Return the PythonTA documentation URL for the given error message id.

    Args:
        msg_id: The five-character error code, e.g. ``"E0401"``.
    """
    return HELP_URL + "#" + msg_id.lower()
