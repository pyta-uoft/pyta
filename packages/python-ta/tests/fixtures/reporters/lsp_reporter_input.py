"""This file is used as a fixture for testing LSPReporter."""


def fun() -> None:
    """Return an expression containing an undefined variable."""
    return "é" + undefined
