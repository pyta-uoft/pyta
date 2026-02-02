"""Utility functions for Z3 integration."""

from __future__ import annotations

import logging
from typing import Any


# NOTE: _debug and parse_assertions are adapted from python_ta.contracts
def _debug(msg: str) -> None:
    """Display a debugging message."""
    logging.basicConfig(format="[%(levelname)s] %(message)s", level=logging.DEBUG)
    logging.debug(msg)


def parse_assertions(obj: Any, parse_token: str = "Precondition") -> list[str]:
    """Return a list of preconditions/postconditions/representation invariants parsed from the given entity's docstring.

    Uses parse_token to determine what to look for. parse_token defaults to Precondition.

    Currently only supports two forms:

    1. A single line of the form "<parse_token>: <cond>"
    2. A group of lines starting with "<parse_token>s:", where each subsequent
       line is of the form "- <cond>". Each line is considered a separate condition.
       The lines can be separated by blank lines, but no other text.
    """
    if hasattr(obj, "doc_node") and obj.doc_node is not None:
        # Check if obj is an astroid node
        docstring = obj.doc_node.value
    else:
        docstring = getattr(obj, "__doc__") or ""
    lines = [line.strip() for line in docstring.split("\n")]
    assertion_lines = [
        i for i, line in enumerate(lines) if line.lower().startswith(parse_token.lower())
    ]

    if assertion_lines == []:
        return []

    first = assertion_lines[0]

    if lines[first].startswith(parse_token + ":"):
        return [lines[first][len(parse_token + ":") :].strip()]
    elif lines[first].startswith(parse_token + "s:"):
        assertions = []
        for line in lines[first + 1 :]:
            if line.startswith("-"):
                assertion = line[1:].strip()
                if hasattr(obj, "__qualname__"):
                    _debug(f"Adding assertion to {obj.__qualname__}: {assertion}")
                assertions.append(assertion)
            elif line != "":
                break
        return assertions
    else:
        return []
