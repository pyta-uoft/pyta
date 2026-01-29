from markupsafe import Markup


class ExtendedMarkup(Markup):
    """
    Extends the standard Markup class defined in markupsafe to include escaping of markdown characters
    """

    @classmethod
    def escape(cls, s):
        """
        Escape all markdown characters in s by replacing them with their corresponding escape sequence
        """
        if isinstance(s, str):
            markdown_chars = [
                "#",  # since the escape sequence contains a #, we should escape the # symbol first to avoid escaping the hash in the escape sequence
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
            for char in markdown_chars:
                ascii = ord(char)
                esc_sequence = f"&#{ascii};"
                s = s.replace(char, esc_sequence)
            return s
