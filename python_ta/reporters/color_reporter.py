import sys

from colorama import Fore, Style, Back
from colorama import init

from .plain_reporter import PlainReporter

# Messages that should be highlighted specially
special = {"missing-docstring",
           "trailing-newlines"}

# Messages without a source code line to highlight
no_hl = {"always-returning-in-a-loop",
         "too-many-nested-blocks"}
    # the "Invalid module name" subsection of "invalid-name" belongs here


class ColorReporter(PlainReporter):
    _SPACE = ' '

    # Override this method to add instance variables
    def __init__(self, number_of_messages, source_lines=None, module_name=''):
        super().__init__(number_of_messages, source_lines, module_name)
        self._sorted_error_messages = {}
        self._sorted_style_messages = {}

    # Override this method
    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)

        self.sort_messages()

        result = self._colourify(Fore.RED + Style.BRIGHT,
                                 '=== Code errors/forbidden usage '
                                 '(fix these right away!) ===\n')
        result += self._colour_messages_by_type(style=False)

        if level == 'all':
            result += '\n' + self._colourify(Fore.BLUE + Style.BRIGHT,
                                             '=== Style/convention errors '
                                             '(fix these before submission) ===\n')
            result += self._colour_messages_by_type(style=True)

        print(result)

    # Override this method
    def sort_messages(self):
        # Sort the messages by their type
        def sort_messages_by_type(messages):
            messages.sort(key=lambda s: s[0])
            sorted_messages = {}
            # Count the number of occurrences and sort the msgs according to their id's
            i = 0
            while i < len(messages):
                current_id = messages[i].msg_id
                count = 1
                sorted_messages[current_id] = [messages[i]]
                while i + 1 < len(messages) and messages[i + 1].msg_id == current_id:
                    count += 1
                    sorted_messages[current_id].append(messages[i + 1])
                    i += 1

                i += 1
            return sorted_messages

        self._sorted_error_messages = sort_messages_by_type(self._error_messages)
        self._sorted_style_messages = sort_messages_by_type(self._style_messages)

    _display = None   # because PyCharm is annoying about this

    def _colour_messages_by_type(self, style=False):
        """
        Return string of properly formatted members of the messages dict
        (error or style) indicated by style.

        NOTE: For each message type's list in _sorted_error_messages and
        _sorted_style_messages, a last element is added that contains the
        length of said list. This is necessary for use in the HTMLReporter's
        template.txt, and is performed after the building of the "result"
        string so as not to affect the printed result of this class.
        WHEN MAKING USE OF THESE LISTS, PLEASE OMIT THE LAST ELEMENT.

        :param bool style: True iff messages is a dict of style messages
        :return: str
        """
        result = ""

        if style:
            messages = self._sorted_style_messages
            fore_colour = Fore.BLUE
        else:
            messages = self._sorted_error_messages
            fore_colour = Fore.RED

        for msg_id in messages:
            code = self._colourify(fore_colour + Style.BRIGHT, msg_id)
            result += code + ' ({})  '.format(messages[msg_id][0].symbol)
            result += 'Number of occurrences: {}.\n\n'.format(len(messages[msg_id]))

            for i, msg in enumerate(messages[msg_id]):
                msg_text = msg.msg
                if msg.symbol == "bad-whitespace":  # fix Pylint inconsistency
                    msg_text = msg_text.partition('\n')[0]
                    messages[msg_id][i] = msg._replace(msg=msg_text)
                    msg = messages[msg_id][i]

                result += 4 * ColorReporter._SPACE
                result += self._colourify(Style.BRIGHT, '[Line {}] {}'.format(
                    msg.line, msg.msg)) + '\n'

                try:
                    # Messages with code snippets
                    if not (msg.symbol in no_hl or
                            msg.msg.startswith("Invalid module") or
                            msg.msg.startswith("Missing module docstring")):

                        if hasattr(msg, "node") and msg.node is not None:
                            start = max(msg.node.fromlineno, 1)
                            end = msg.node.end_lineno
                        else:
                            # Some message types don't have a node, including:
                            # - line-too-long
                            # - bad-whitespace
                            # - trailing-newlines
                            start = end = msg.line

                        result += '\n' + 4 * ColorReporter._SPACE
                        result += self._colourify(Style.BRIGHT,
                                                  'Your Code Starts Here:\n')
                        result += '\n'

                        code_snippet = ""

                        # Non-special prints first error line with 'e', other
                        # lines with 'o'.
                        # Special prints each message specially.
                        # Both print 2 lines of context before and after
                        # (code boundaries permitting).

                        # Print up to 2 lines before start - 1 for context:
                        for l in range(max(start - 3, 0), start - 1):
                            code_snippet += self._add_line(msg, l, 'c')

                        if msg.symbol == "trailing-newlines":
                            code_snippet += self._add_line(msg, start - 1, 'n')
                        elif msg.msg.startswith("Missing function docstring"):
                            code_snippet += self._add_line(
                                msg, start - 1, 'e')
                            code_snippet += self._add_line(msg, start, '.')
                        else:  # so msg isn't in special at all
                            code_snippet += self._add_line(msg, start - 1, 'e')
                            for line in range(start, end):
                                code_snippet += self._add_line(msg, line, 'o')

                        # Print up to 2 lines after end - 1 for context:
                        for l in range(end, min(end + 2, len(self._source_lines))):
                            code_snippet += self._add_line(msg, l, 'c')

                        result += code_snippet + '\n'
                        try:
                            messages[msg_id][i] = msg._replace(snippet=code_snippet)
                        except ValueError as e:
                            # raise ValueError("Non-NewMessage message has "
                            #                  "no 'snippet' attribute") from e
                            pass

                except AttributeError:
                    pass

                result += '\n'
            messages[msg_id].append(len(messages[msg_id]))  # for HTMLReporter use
        return result

    def _add_line(self, msg, n, linetype):
        """
        Format given source code line as specified and return as str.
        Use linetype='n' to print only the highlighted line number of the line.
        Use linetype='.' to elide line (with proper indentation).

        Called by _colour_messages_by_type, relies on _colourify.

        :param int n: index of line in self._source_lines to add
        :param str linetype: e/c/o/n/. for error/context/other/number-only/ellipsis
        :return: str
        """
        snippet = ""
        space = ColorReporter._SPACE

        text = self._source_lines[n].rstrip('\n\r')
        # Pad line number with spaces to even out indent:
        number = self._colourify(Fore.LIGHTBLACK_EX, "{:>3}".format(n + 1))

        if linetype == "e":  # (error)
            snippet += 4 * space + self._colourify(Style.BRIGHT, number)
            if hasattr(msg, "node") and msg.node is not None:
                start_col = msg.node.col_offset
                end_col = msg.node.end_col_offset
            else:
                # to prevent highlighted indent
                start_col = -len(text.lstrip(' '))  # negative to count from end
                end_col = len(text)

            snippet += 4 * space + text[:start_col]
            snippet += self._colourify(Style.BRIGHT + Fore.BLACK + Back.CYAN,
                                       text[start_col:end_col])
            snippet += text[end_col:]

        elif linetype == "c":  # (context)
            snippet += 4 * space + number
            snippet += 4 * space + self._colourify(Fore.LIGHTBLACK_EX, text)

        elif linetype == "o":  # (other)
            snippet += 4 * space + number
            snippet += 4 * space + text

        elif linetype == "n":  # (number only)
            snippet += 4 * space + self._colourify(
                Style.BRIGHT + Fore.BLACK + Back.CYAN, number)

        elif linetype == '.':  # (ellipsis)
            snippet += 4 * space + number
            snippet += 4 * space
            spaces = len(text) - len(text.lstrip(' '))
            snippet += spaces * space
            snippet += self._colourify(Style.BRIGHT + Fore.BLACK + Back.CYAN,
                                       '...')

        else:
            print("ERROR")

        snippet += '\n'

        return snippet

    @staticmethod
    def _colourify(colour, text):
        """
        Adds given ANSI colouring tokens to text as well as final colour reset.

        Called by _colour_messages_by_type and _add_line.

        :param str colour: colorama ANSI code(s)
        :param str text: text to be coloured
        :return str
        """
        return colour + text + Style.RESET_ALL  # + Fore.RESET + Back.RESET
