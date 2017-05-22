from pylint.reporters import BaseReporter
from pylint.utils import Message
from collections import defaultdict, namedtuple
from enum import Enum

NewMessage = namedtuple('NewMessage', Message._fields + ('node', 'snippet'))

# Checks to enable for basic_check (trying to find errors
# and forbidden constructs only)
ERROR_CHECKS = [
    'used-before-assignment',
    'undefined-variable',
    'undefined-loop-variable',
    'not-in-loop',
    'return-outside-function',
    'duplicate-key',
    'unreachable',
    'pointless-statement',
    'pointless-string-statement',
    'no-member',
    'not-callable',
    'assignment-from-no-return',
    'assignment-from-none',
    'no-value-for-parameter',
    'too-many-function-args',
    'invalid-sequence-index',
    'invalid-slice-index',
    'invalid-unary-operand-type',
    'unsupported-binary-operation',
    'unsupported-membership-test',
    'unsubscriptable-object',
    'unbalanced-tuple-unpacking',
    'unpacking-non-sequence',
    'function-redefined',
    'duplicate-argument-name',
    'import-error',
    'no-name-in-module',
    'non-parent-init-called',
    'access-member-before-definition',
    'method-hidden',
    'unexpected-special-method-signature',
    'inherit-non-class',
    'duplicate-except',
    'bad-except-order',
    'raising-bad-type',
    'raising-non-exception',
    'catching-non-exception',
    'bad-indentation',
    'E9996',
    'E9991',
    'E0001',
    'E9999'
]


# Messages that should be highlighted specially
special = {'missing-docstring',
           'trailing-newlines'}

# Messages without a source code line to highlight
no_hl = {'always-returning-in-a-loop',
         'too-many-nested-blocks'}
    # the "Invalid module name" subsection of "invalid-name" belongs here


class PlainReporter(BaseReporter):
    _SPACE = ' '
    _BREAK = '\n'
    _COLOURING = {}

    def __init__(self, source_lines=None, module_name=''):
        super().__init__()
        self._error_messages = []
        self._style_messages = []
        self._source_lines = source_lines or []
        self._module_name = module_name
        self.linter = None
        self._sorted_error_messages = defaultdict(list)
        self._sorted_style_messages = defaultdict(list)

    def reset_messages(self):
        """Reset the reporter's messages, for multiple files."""
        self._error_messages = []
        self._style_messages = []
        self._sorted_error_messages.clear()
        self._sorted_style_messages.clear()

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        if msg.msg_id in ERROR_CHECKS or msg.symbol in ERROR_CHECKS:
            self._error_messages.append(msg)
        else:
            self._style_messages.append(msg)

    def handle_node(self, msg, node):
        """Add node attribute to last message."""
        if msg.msgid in ERROR_CHECKS or msg.symbol in ERROR_CHECKS:
            if (self._error_messages and
                    self._error_messages[-1].msg_id == msg.msgid and
                    not isinstance(self._error_messages[-1], NewMessage)):
                self._error_messages[-1] = NewMessage(*self._error_messages[-1], node, '')
        else:
            if (self._style_messages and
                    self._style_messages[-1].msg_id == msg.msgid and
                    not isinstance(self._style_messages[-1], NewMessage)):
                self._style_messages[-1] = NewMessage(*self._style_messages[-1], node, '')

    def sort_messages(self):
        """Sort the messages by their type (message id)."""
        for msg in self._error_messages:
            self._sorted_error_messages[msg.msg_id].append(msg)
        for msg in self._style_messages:
            self._sorted_style_messages[msg.msg_id].append(msg)

    def show_file_linted(self, filename):
        print('*'*15, 'File:', filename)

    def print_messages(self, level='all'):
        self.sort_messages()

        result = self._colourify('code-heading',
                                 '=== Code errors/forbidden usage '
                                 '(fix: high priority) ===' + self._BREAK)
        messages_result = self._colour_messages_by_type(style=False)
        if messages_result:
            result += messages_result
        else:
            result += 'None!' + self._BREAK*2

        if level == 'all':
            result += self._colourify('style-heading',
                                      '=== Style/convention errors '
                                      '(fix: before submission) ===' + self._BREAK)
            messages_result = self._colour_messages_by_type(style=True)
            if messages_result:
                result += messages_result
            else:
                result += 'None!' + self._BREAK*2

        print(result)

    def _colour_messages_by_type(self, style=False):
        """
        Return string of properly formatted members of the messages dict
        (error or style) indicated by style.
    
        :param bool style: True iff messages is a dict of style messages
        :return: str
        """
        if style:
            messages = self._sorted_style_messages
            fore_colour = 'style-name'
        else:
            messages = self._sorted_error_messages
            fore_colour = 'code-name'

        max_messages = self.linter.config.pyta_number_of_messages

        result = ''
        for msg_id in messages:
            result += self._colourify(fore_colour, msg_id)
            result += self._colourify('bold', ' ({})  '.format(messages[msg_id][0].symbol))
            result += 'Number of occurrences: {}.{}'.format(len(messages[msg_id]), self._BREAK)
            if max_messages != float('inf') and max_messages < len(messages[msg_id]):
                result += ' First {} shown.'.format(max_messages)

            for i, msg in enumerate(messages[msg_id]):
                if i == max_messages:
                    break
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
        if not self._source_lines:
            return ''

        snippet = ''
        spaces = 2 * self._SPACE
        text = self._source_lines[n]
        # Pad line number with spaces to even out indent:
        number = '{:>3}'.format(n + 1)

        # Set starting and ending columns.
        if hasattr(msg, 'node') and msg.node is not None:
            start_col = msg.node.col_offset
            end_col = msg.node.end_col_offset
        else:
            # to prevent highlighted indent
            start_col = -len(text.lstrip(' '))  # negative to count from end
            end_col = len(text)

        if linetype == LineType.ERROR:
            snippet += spaces + self._colourify('gbold', number)
            snippet += spaces + self._colourify('black', text[:start_col])
            snippet += self._colourify('highlight',
                                       text[start_col:end_col])
            snippet += self._colourify('black', text[end_col:])
        elif linetype == LineType.CONTEXT:
            snippet += spaces + self._colourify('grey', number) + spaces + self._colourify('grey', text)

        elif linetype == LineType.OTHER:
            snippet += spaces + self._colourify('grey', number) + spaces + text

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
        return text

    _display = None


class LineType(Enum):
    """ An enumeration for _add_line method line types. """
    ERROR = 1       # line with error
    CONTEXT = 2     # non-error/other line added for context
    OTHER = 3       # line included in source but not error
    NUMBERONLY = 4  # only highlighted line number
    ELLIPSIS = 5    # code replaced with ellipsis
    DOCSTRING = 6   # docstring needed warning
