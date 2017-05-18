from pylint.reporters import BaseReporter
from pylint.utils import Message
from collections import namedtuple

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


class PlainReporter(BaseReporter):

    name = 'plain'

    def __init__(self, source_lines=None, module_name=''):
        super().__init__()
        self._error_messages = []
        self._style_messages = []
        self._source_lines = source_lines or []
        self._module_name = module_name
        self.linter = None

    def reset_messages(self):
        """Reset the reporter's messages, for multiple files."""
        self._error_messages = []
        self._style_messages = []

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

    def print_messages(self, level='all'):
        self.sort_messages()
        print('=== Code errors/forbidden usage (fix: high priority) ===')
        if not self._error_messages:
            print('None!')
        for msg in self._error_messages:
            code = msg.msg_id
            print(code, '({})  {}\n    [Line {}] {}'.format(msg.symbol, msg.obj, msg.line, msg.msg))

        if level == 'all':
            print('\n')
            print('=== Style/convention errors (fix: before submission) ===')
            if not self._style_messages:
                print('None!')
            for msg in self._style_messages:
                code = msg.msg_id
                print(code, '({})  {}\n    [Line {}] {}'.format(msg.symbol, msg.obj, msg.line, msg.msg))
        print('\n')

    def sort_messages(self):
        max_messages = float('inf')
        if self.linter and self.linter.config.number_of_messages:
            max_messages = self.linter.config.number_of_messages

        # Sort the messages by their type.
        for message_list in [self._error_messages, self._style_messages]:
            message_list.sort(key=lambda s: s[0])

            i = 0
            while i < len(message_list):
                current_id = message_list[i].msg_id
                count = 1
                messages = []
                while i + 1 < len(message_list) and message_list[i + 1].msg_id == current_id:
                    count += 1
                    if len(messages) < max_messages - 1:
                        messages.append('[Line {}] {}'.format(message_list[i + 1].line, message_list[i + 1].msg))
                    message_list.pop(i + 1)

                msg_new = message_list[i].msg

                if len(messages) > 0:
                    msg_new = message_list[i].msg + '\n    ' + '\n    '.join(messages)

                obj_new = 'Number of occurrences: {}.'.format(count)

                if max_messages < count and max_messages != float('inf'):
                    obj_new = obj_new + ' First {} shown.'.format(max_messages)

                message_list[i] = message_list[i]._replace(msg=msg_new, obj=obj_new)
                i += 1

    def show_file_linted(self, filename):
        print('*'*15, 'File:', filename)

    _display = None
