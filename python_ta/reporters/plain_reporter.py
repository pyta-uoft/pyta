import sys
import os
from pylint.reporters import BaseReporter
from pylint.utils import Message
from collections import defaultdict, namedtuple
from .node_printers import LineType, render_message

OUTPUT_FILENAME = 'pyta_output'
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
    'E9999',
    'unexpected-keyword-arg',
    'not-an-iterable',
    'nonexistent-operator',
    'invalid-length-returned',
    'abstract-method'
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
    code_err_title = '=== Code errors/forbidden usage (fix: high priority) ==='
    style_err_title = '=== Style/convention errors (fix: before submission) ==='
    no_err_message = 'None!' + _BREAK * 2
    no_snippet = 'Nothing here.' + _BREAK * 2

    def __init__(self, source_lines=None, module_name=''):
        """Reminder: see pylint BaseReporter for other instance variables init.
        """
        super().__init__()
        self._error_messages = []
        self._style_messages = []
        self._source_lines = source_lines or []
        self._module_name = module_name
        self._sorted_error_messages = defaultdict(list)
        self._sorted_style_messages = defaultdict(list)
        self._output_filepath = None
        self.current_file_linted = None

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

    def set_output_filepath(self, output_filepath_arg):
        """Save location to output pyta messages, if any."""
        if output_filepath_arg is None:
            return

        # Paths may contain system-specific or relative syntax, e.g. `~`, `../`
        correct_path = os.path.expanduser(output_filepath_arg)
        if not os.path.exists(os.path.dirname(correct_path)):
            raise IOError('path {} does not exist.'.format(output_filepath_arg))
        if os.path.isdir(correct_path):
            correct_path = os.path.join(correct_path, OUTPUT_FILENAME)

        # Save output location and remove it if exists from previous run.
        self._output_filepath = correct_path
        # Remove existing file to prepare for appending messages from recursive
        # linting of files.
        if os.path.exists(correct_path):
            os.remove(correct_path)

    def filename_to_display(self, filename):
        """Display the file name, currently consistent with pylint format."""
        return '{}'.format(filename)

    def register_file(self, filename):
        """Register information of the linted file, for later use by reporter"""
        self.current_file_linted = filename

        # Augment the reporter with the source code.
        with open(filename, encoding='utf-8') as f:
            self._source_lines = [
                line.rstrip() for line in f.readlines()]

    def print_messages(self, level='all'):
        self.sort_messages()

        result = self._colourify('code-heading', self.code_err_title + self._BREAK)
        messages_result = self._colour_messages_by_type(style=False)
        if messages_result:
            result += messages_result
        else:
            result += self.no_err_message

        if level == 'all':
            result += self._colourify('style-heading', self.style_err_title + self._BREAK)
            messages_result = self._colour_messages_by_type(style=True)
            if messages_result:
                result += messages_result
            else:
                result += self.no_err_message

        output_stream = sys.stdout
        if self._output_filepath:
            output_stream = open(self._output_filepath, 'a')
        print(self.filename_to_display(self.current_file_linted), file=output_stream)
        print(result, file=output_stream)
        if self._output_filepath:
            output_stream.close()

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
            result += 'Number of occurrences: {}.'.format(len(messages[msg_id]))
            if max_messages != float('inf') and max_messages < len(messages[msg_id]):
                result += ' (First {} shown).'.format(max_messages)
            result += self._BREAK

            for i, msg in enumerate(messages[msg_id]):
                if i == max_messages:
                    break

                # Use only explanation, without redundant accessory information
                msg_truncated = msg.msg.split('\n')[0]
                result += 2 * self._SPACE
                result += self._colourify('bold', '[Line {}] {}'
                            .format(msg.line, msg_truncated)) + self._BREAK

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
        code_snippet = ''

        for line, slice_, line_type, text in render_message(msg, self._source_lines):
            code_snippet += self._add_line(line, line_type, slice_, text)

        return code_snippet

    def _add_line(self, n, linetype, slice_, text=''):
        """
        Format given source code line as specified and return as str.

        Called by _colour_messages_by_type, relies on _colourify.
        Now applicable both to ColorReporter and HTMLReporter.

        :param int n: index of line in self._source_lines to add
        :param LineType linetype: enum member indicating way to format line
        :return: str
        """
        snippet = self._add_line_number(n, linetype)

        # Set starting and ending columns.
        start_col = slice_.start or 0
        end_col = slice_.stop or len(text)

        if linetype == LineType.ERROR:
            snippet += self._colourify('black', text[:start_col])
            snippet += self._colourify('highlight', text[slice_])
            snippet += self._colourify('black', text[end_col:])
        elif linetype == LineType.CONTEXT:
            snippet += self._colourify('grey', text)
        elif linetype == LineType.OTHER:
            snippet += text
        elif linetype == LineType.DOCSTRING:
            space_c = len(text) - len(text.lstrip(' '))
            snippet += space_c * self._SPACE
            snippet += self._colourify('highlight', text.lstrip(' '))

        snippet += self._BREAK
        return snippet

    def _add_line_number(self, n, linetype):
        """Return a formatted string displaying a line number."""
        spaces = 2 * self._SPACE
        if n is not None:
            number = '{:>3}'.format(n)
        else:
            number = 3 * self._SPACE

        if linetype == LineType.ERROR:
            return spaces + self._colourify('gbold', number) + spaces
        elif linetype == LineType.CONTEXT:
            return spaces + self._colourify('grey', number) + spaces
        elif linetype == LineType.OTHER:
            return spaces + self._colourify('grey', number) + spaces
        elif linetype == LineType.DOCSTRING:
            return spaces + self._colourify('black', number) + spaces
        else:
            return spaces + number + spaces

    @classmethod
    def _colourify(cls, colour_class, text):
        return text

    _display = None

    def output_blob(self):
        """Override in reporters that output collections of messages once at
        the end of linting all files, rather than stream to std.out"""
        pass
