from typing import Any

from markupsafe import Markup

markdown_chars = [
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
unmapped_code_point = "\ue000"


class ExtendedMarkup(Markup):
    """Extends the standard Markup class defined in markupsafe to include escaping of markdown characters"""

    @classmethod
    def escape(cls: type["ExtendedMarkup"], s: Any) -> str:
        """Escape all markdown characters in s by replacing them with their corresponding escape sequence"""
        if isinstance(s, str):
            for char in markdown_chars:
                ascii = ord(char)
                esc_sequence = f"{unmapped_code_point}#{ascii};"
                s = s.replace(char, esc_sequence)
                return s
        else:
            return str(s)
