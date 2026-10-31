"""
Report enabled PythonTA messages that are missing from the PythonTA documentation.

Run this script from the repository root with:
    uv run scripts/check_message_documentation.py

This script exits with status 1 when any documentation is missing, or 0 when all enabled
messages have documentation. It checks all Pylint and PythonTA messages using
PythonTA's default configuration and the installed Pylint version.

It includes all enabled message definitions, even when reporting them requires additional
configuration, such as z3=True. Known messages that remain registered but are no longer
emitted are explicitly excluded.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from python_ta.check.helpers import reset_linter

DEFAULT_DOCS_PATH = (
    Path(__file__).resolve().parents[1] / "packages/python-ta/docs/checkers/index.md"
)

# These messages will be ignored by this script.
# Document the reason and supporting source for each exclusion.
EXCLUDED_MESSAGES = {
    # No longer emitted since Pylint's configuration parser changed in version 2.14.
    # https://pylint.readthedocs.io/en/stable/user_guide/messages/error/bad-configuration-section.html
    "E0014",
}


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

    # Exclude known retired diagnostics before checking documentation coverage.
    ignored = enabled.keys() & EXCLUDED_MESSAGES
    checked = enabled.keys() - ignored
    missing = sorted(checked - documented)

    print(f"Enabled messages: {len(enabled)}")
    print(f"Ignored messages no longer emitted: {len(ignored)}")
    print(f"Enabled messages with documentation: {len(checked & documented)}")
    print(f"Missing documentation: {len(missing)}")
    for msg_id in missing:
        print(f"{msg_id}: {enabled[msg_id]}")

    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
