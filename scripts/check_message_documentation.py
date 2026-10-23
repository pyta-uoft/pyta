"""
Report enabled PythonTA messages that are missing from the PythonTA documentation.

Run this script from the repository root with:
    uv run scripts/check_message_documentation.py

This script exits with status 1 when any documentation is missing, or 0 when all enabled
messages have documentation. It checks all Pylint and PythonTA messages using
PythonTA's default configuration and the installed Pylint version.

It includes all enabled message definitions, even when reporting them requires additional
configuration, such as z3=True.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from python_ta.check.helpers import reset_linter

DEFAULT_DOCS_PATH = (
    Path(__file__).resolve().parents[1] / "packages/python-ta/docs/checkers/index.md"
)


def main() -> int:
    """Print missing message IDs and symbols, returning a shell exit status."""

    # Read from actual documentation
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--docs",
        type=Path,
        default=DEFAULT_DOCS_PATH,
        help="checker documentation to audit (defaults to this checkout's documentation)",
    )
    args = parser.parse_args()
    try:
        documentation = args.docs.read_text(encoding="utf-8")
    except OSError as error:
        parser.error(str(error))

    # Match documentation message codes
    documented = set(re.findall(r"^\(([CEFIRW]\d{4})\)=[ \t]*$", documentation, re.MULTILINE))

    # Collect all enabled messages
    linter = reset_linter(config={}, load_default_config=True)
    enabled = {
        message.msgid: message.symbol
        for message in linter.msgs_store.messages
        if linter.is_message_enabled(message.msgid)
    }

    # Calculate and output the messages with missing documentation
    missing = sorted(enabled.keys() - documented)

    print(f"Enabled messages: {len(enabled)}")
    print(f"Enabled messages with documentation: {len(enabled.keys() & documented)}")
    print(f"Missing documentation: {len(missing)}")
    for msg_id in missing:
        print(f"{msg_id}: {enabled[msg_id]}")

    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
