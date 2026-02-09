from typing import Any

from markupsafe import Markup

MARKDOWN_CHARS = [
    "`",
    "#",
    "\\",
    "*",
    "_",
    "{",
    "}",
    "[",
    "]",
    "(",
    ")",
    ".",
    "!",
    "|",
    "~",
    ":",
]
UNMAPPED_CODE_POINT = "\ue000"


class ExtendedMarkup(Markup):
    """Extends the standard Markup class defined in markupsafe to include escaping of markdown characters"""

    @classmethod
    def escape(cls: type["ExtendedMarkup"], s: Any) -> str:
        """Escape all markdown characters in s by replacing them with their corresponding escape sequence"""
        if isinstance(s, str):
            for char in MARKDOWN_CHARS:
                ascii = ord(char)
                esc_sequence = f"{UNMAPPED_CODE_POINT}#{ascii};"
                s = s.replace(char, esc_sequence)
                return s
        else:
            return str(s)
