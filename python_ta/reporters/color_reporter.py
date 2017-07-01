import sys
from colorama import Fore, Style, Back, init
from .plain_reporter import PlainReporter


class ColorReporter(PlainReporter):
    _SPACE = ' '
    _BREAK = '\n'
    _COLOURING = {'black': Fore.BLACK,  # or could be empty
                  'bold': Style.BRIGHT,
                  'code-heading': Fore.RED + Style.BRIGHT,
                  'style-heading': Fore.BLUE + Style.BRIGHT,
                  'code-name': Fore.RED + Style.BRIGHT,
                  'style-name': Fore.BLUE + Style.BRIGHT,
                  'highlight': Style.BRIGHT + Fore.BLACK + Back.CYAN,
                  'grey': Fore.LIGHTBLACK_EX,
                  'gbold': Style.BRIGHT + Fore.LIGHTBLACK_EX,
                  'reset': Style.RESET_ALL}

    def __init__(self, source_lines=None, module_name=''):
        super().__init__(source_lines, module_name)

    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)
        super().print_messages(level)

    @classmethod
    def _colourify(cls, colour_class, text):
        """
        Adds given ANSI colouring tokens (or key to colouring tokens in the
        class-level dict "_COLOURING") to text as well as final colour reset.

        Does not colour indents, except non-space indents.
        Called by _colour_messages_by_type and _add_line.
        Now applicable both to ColorReporter and HTMLReporter.

        :param str colour_class: key to colour class or ANSI colour token(s)
        :param str text: text to be coloured
        :return str
        """
        colour = cls._COLOURING[colour_class]
        new_text = text.lstrip(' ')
        space_count = len(text) - len(new_text)
        if cls._SPACE != ' ':
            new_text = new_text.replace(' ', cls._SPACE)
        return ((space_count * cls._SPACE) + colour + new_text +
                cls._COLOURING['reset'])

    _display = None   # because PyCharm is annoying about this
