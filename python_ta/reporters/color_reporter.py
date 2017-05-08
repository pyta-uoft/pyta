import sys
from collections import defaultdict
from enum import Enum

from colorama import Fore, Style, Back
from colorama import init

from .plain_reporter import PlainReporter

# Messages that should be highlighted specially
special = {'missing-docstring',
           'trailing-newlines'}

# Messages without a source code line to highlight
no_hl = {'always-returning-in-a-loop',
         'too-many-nested-blocks'}
    # the "Invalid module name" subsection of "invalid-name" belongs here


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

    # Override this method to add instance variables
    def __init__(self, number_of_messages, source_lines=None, module_name=''):
        super().__init__(number_of_messages, source_lines, module_name)
        self._sorted_error_messages = defaultdict(list)
        self._sorted_style_messages = defaultdict(list)

    def reset_messages(self):
        super().reset_messages()
        self._sorted_error_messages.clear()
        self._sorted_style_messages.clear()

    # Override this method
    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)

        self.sort_messages()

        result = self._colourify('code-heading',
                                 '=== Code errors/forbidden usage '
                                 '(fix: high priority) ===' + self._BREAK)
        messages_result = self._colour_messages_by_type(style=False)
        result += messages_result
        if not messages_result:
            result += 'None!\n\n'

        if level == 'all':
            result += self._colourify('style-heading',
                                      '=== Style/convention errors '
                                      '(fix: before submission) ===' + self._BREAK)
            messages_result = self._colour_messages_by_type(style=True)
            result += messages_result
            if not messages_result:
                result += 'None!\n\n'

        print(result)

    # Override this method
    def sort_messages(self):
        # Sort the messages by their type (message id)
        def sort_messages_by_type(messages, sorted_messages):
            i = 0
            while i < len(messages):
                current_id = messages[i].msg_id
                while i < len(messages) and messages[i].msg_id == current_id:
                    sorted_messages[current_id].append(messages[i])
                    i += 1

        sort_messages_by_type(self._error_messages, self._sorted_error_messages)
        sort_messages_by_type(self._style_messages, self._sorted_style_messages)

    _display = None   # because PyCharm is annoying about this

    def _colour_messages_by_type(self, style=False):
        """
        Return string of properly formatted members of the messages dict
        (error or style) indicated by style.

        :param bool style: True iff messages is a dict of style messages
        :return: str
        """
        result = ''

        if style:
            messages = self._sorted_style_messages
            fore_colour = 'style-name'
        else:
            messages = self._sorted_error_messages
            fore_colour = 'code-name'

        for msg_id in messages:
            result += self._colourify(fore_colour, msg_id)
            result += self._colourify('bold', ' ({})  '.format(messages[msg_id][0].symbol))
            result += 'Number of occurrences: {}.{}'.format(len(messages[msg_id]), self._BREAK)

            for i, msg in enumerate(messages[msg_id]):
                msg_text = msg.msg
                if msg.symbol == 'bad-whitespace':  # fix Pylint inconsistency
                    msg_text = msg_text.partition('\n')[0]
                    messages[msg_id][i] = msg._replace(msg=msg_text)
                    msg = messages[msg_id][i]

                result += 2 * self._SPACE
                result += self._colourify('bold', '[Line {}] {}'
                            .format(msg.line, msg.msg)) + self._BREAK

                try:
                    # Messages with code snippets
                    if not (msg.symbol in no_hl or
                            msg.msg.startswith('Invalid module')):
                        code_snippet = self._build_snippet(msg)
                        result += code_snippet
                        try:
                            messages[msg_id][i] = msg._replace(snippet=code_snippet)
                        except ValueError:
                            pass
                except AttributeError:
                    pass
                result += self._BREAK

        return result

    def _build_snippet(self, msg):
        """
        Generates and returns a code snippet for the given Message object,
        formatted appropriately according to line type.

        :param Message msg: the message for which a code snippet is built
        :return: str
        """
        if hasattr(msg, 'node') and msg.node is not None:
            start = max(msg.node.fromlineno, 1)
            end = msg.node.end_lineno
        else:
            # Some message types don't have a node, including:
            # - line-too-long
            # - bad-whitespace
            # - trailing-newlines
            start = end = msg.line

        code_snippet = ''

        # Non-special prints first error line with 'e', other
        # lines with 'o'.
        # Special prints each message specially.
        # Both print 2 lines of context before and after
        # (code boundaries permitting).

        # Print up to 2 lines before start - 1 for context:
        for l in range(max(start - 3, 0), start - 1):
            code_snippet += self._add_line(msg, l, LineType.CONTEXT)

        if msg.symbol == 'trailing-newlines':
            code_snippet += self._add_line(msg, start - 1, LineType.NUMBERONLY)
        elif msg.msg.startswith('Missing function docstring'):
            code_snippet += self._add_line(
                msg, start - 1, LineType.ERROR)
            code_snippet += self._add_line(msg, start, LineType.DOCSTRING)
            end = start  # to print context after function header
        elif msg.msg.startswith('Missing module docstring'):
            # Perhaps instead of start, use line 0?
            code_snippet += self._add_line(msg, start - 1, LineType.DOCSTRING)
            end = 0  # to print context after
        else:  # so msg isn't in special at all
            code_snippet += self._add_line(msg, start - 1, LineType.ERROR)
            for line in range(start, end):
                code_snippet += self._add_line(msg, line, LineType.OTHER)

        # Print up to 2 lines after end - 1 for context:
        for l in range(end, min(end + 2, len(self._source_lines))):
            code_snippet += self._add_line(msg, l, LineType.CONTEXT)

        return code_snippet

    def _add_line(self, msg, n, linetype):
        """
        Format given source code line as specified and return as str.

        Called by _colour_messages_by_type, relies on _colourify.
        Now applicable both to ColorReporter and HTMLReporter.

        :param int n: index of line in self._source_lines to add
        :param LineType linetype: enum member indicating way to format line
        :return: str
        """
        snippet = ''
        spaces = 2 * self._SPACE
        if not self._source_lines: 
            return ''
        text = self._source_lines[n].rstrip('\n\r')
        # Pad line number with spaces to even out indent:
        number = '{:>3}'.format(n + 1)

        if linetype == LineType.ERROR:
            snippet += spaces + self._colourify('gbold', number)
            if hasattr(msg, 'node') and msg.node is not None:
                start_col = msg.node.col_offset
                end_col = msg.node.end_col_offset
            else:
                # to prevent highlighted indent
                start_col = -len(text.lstrip(' '))  # negative to count from end
                end_col = len(text)

            snippet += spaces + self._colourify('black', text[:start_col])
            snippet += self._colourify('highlight',
                                       text[start_col:end_col])
            snippet += self._colourify('black', text[end_col:])

        elif linetype == LineType.CONTEXT:
            snippet += spaces + self._colourify('grey', number)
            snippet += spaces + self._colourify('grey', text)

        elif linetype == LineType.OTHER:
            snippet += spaces + self._colourify('grey', number)
            snippet += spaces + text

        elif linetype == LineType.NUMBERONLY:
            snippet += spaces + self._colourify('highlight', number)

        elif linetype == LineType.ELLIPSIS:
            snippet += spaces + self._colourify('gbold', number)
            snippet += spaces
            space_c = len(text) - len(text.lstrip(' '))
            snippet += space_c * self._SPACE
            snippet += self._colourify('black', '. . .')
            # Need spaces in between dots to prevent PyCharm thinking
            # that the '...' is actually a line-continuation prompt.

        elif linetype == LineType.DOCSTRING:
            snippet += self._SPACE * 7  # 2-space indent, 3-space number, 2-space indent
            space_c = len(text) - len(text.lstrip(' '))
            snippet += space_c * self._SPACE
            snippet += self._colourify('highlight',
                                       '""" YOUR DOCSTRING HERE """')

        snippet += self._BREAK
        return snippet

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


class LineType(Enum):
    """ An enumeration for _add_line method line types. """
    ERROR = 1       # line with error
    CONTEXT = 2     # non-error/other line added for context
    OTHER = 3       # line included in source but not error
    NUMBERONLY = 4  # only highlighted line number
    ELLIPSIS = 5    # code replaced with ellipsis
    DOCSTRING = 6   # docstring needed warning
