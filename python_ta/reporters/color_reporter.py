import sys

from colorama import Back, Fore, Style, colorama_text
from pylint.interfaces import IReporter

from .node_printers import LineType
from .plain_reporter import PlainReporter


class ColorReporter(PlainReporter):
    """Colorized text reporter. Should only be used to print to stdout."""

    name = "ColorReporter"

    _COLOURING = {
        "black": Fore.BLACK,
        "black-line": Fore.BLACK,
        "bold": Style.BRIGHT,
        "code-heading": Fore.RED + Style.BRIGHT,
        "style-heading": Fore.BLUE + Style.BRIGHT,
        "code-name": Fore.RED + Style.BRIGHT,
        "style-name": Fore.BLUE + Style.BRIGHT,
        "highlight": Style.BRIGHT + Fore.BLACK + Back.CYAN,
        "grey": Fore.LIGHTBLACK_EX,
        "grey-line": Fore.LIGHTBLACK_EX,
        "gbold": Style.BRIGHT + Fore.LIGHTBLACK_EX,
        "gbold-line": Style.BRIGHT + Fore.LIGHTBLACK_EX,
        "reset": Style.RESET_ALL,
    }

    def print_messages(self, level: str = "all") -> None:
        """Print messages for the current file.

        If level == 'all', both errors and style errors are displayed. Otherwise,
        only errors are displayed.
        """
        # Check if the OS currently running is Windows
        with colorama_text(wrap=(sys.platform == "win32"), strip=False):
            super().print_messages(level)

    def _add_line(self, lineno: int, linetype: LineType, slice_: slice, text: str = "") -> str:
        """Format given source code line as specified and return as str.

        Called by _build_snippet, relies on _colourify.
        """
        snippet = self._add_line_number(lineno, linetype)

        if linetype == LineType.ERROR:
            start_col = slice_.start or 0
            end_col = slice_.stop or len(text)

            if text[:start_col]:
                snippet += self._colourify("black", text[:start_col])
            snippet += self._colourify("highlight", text[slice_])
            if text[end_col:]:
                snippet += self._colourify("black", text[end_col:])
        elif linetype == LineType.CONTEXT:
            snippet += self._colourify("grey", text)
        elif linetype == LineType.OTHER:
            snippet += text
        elif linetype == LineType.DOCSTRING:
            space_c = len(text) - len(text.lstrip(" "))
            snippet += space_c * self._SPACE
            snippet += self._colourify("highlight", text.lstrip(" "))

        snippet += self._BREAK
        return snippet

    @classmethod
    def _colourify(cls, colour_class: str, text: str) -> str:
        """
        Adds given ANSI colouring tokens (or key to colouring tokens in the
        class-level dict "_COLOURING") to text as well as final colour reset.

        Does not colour indents, except non-space indents.
        Called by _colour_messages_by_type and _add_line.
        """
        colour = cls._COLOURING[colour_class]
        new_text = text.lstrip(" ")
        space_count = len(text) - len(new_text)
        new_text = new_text.replace(" ", cls._SPACE)
        return (space_count * cls._SPACE) + colour + new_text + cls._COLOURING["reset"]
