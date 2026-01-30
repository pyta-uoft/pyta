from typing import Self

from markupsafe import Markup

markdown_chars = [
    "#",
    "\\",
    "`",
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


class ExtendedMarkup(Markup):
    """Extends the standard Markup class defined in markupsafe to include escaping of markdown characters"""

    @classmethod
    def escape(cls: type[Self], s: str) -> str:
        """Escape all markdown characters in s by replacing them with their corresponding escape sequence"""
        if isinstance(s, str):
            for char in markdown_chars:
                ascii = ord(char)
                esc_sequence = f"\ue000#{ascii};"
                s = s.replace(char, esc_sequence)
                return s
        else:
            return str(s)
