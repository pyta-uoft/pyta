from pylint.reporters import BaseReporter


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
    def __init__(self, number_of_messages):
        super().__init__(self)
        self._error_messages = []
        self._style_messages = []
        self._number_of_messages = number_of_messages

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        if msg.msg_id in ERROR_CHECKS or msg.symbol in ERROR_CHECKS:
            self._error_messages.append(msg)
        else:
            self._style_messages.append(msg)

    def print_messages(self, level='all'):
        # Sort the messages.
        self.sort_messages()
        print('=== Code errors/forbidden usage (fix these right away!) ===')
        for msg in self._error_messages:
            code = msg.msg_id
            print(code, '({})  {}\n    [Line {}] {}'.format(msg.symbol, msg.obj, msg.line, msg.msg))

        if level == 'all':
            print('\n')
            print('=== Style/convention errors (fix these before submission) ===')
            for msg in self._style_messages:
                code = msg.msg_id
                print(code, '({})  {}\n    [Line {}] {}'.format(msg.symbol, msg.obj, msg.line, msg.msg))

    def sort_messages(self):
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
                    if self._number_of_messages == 0:
                        messages.append('[Line {}] {}'.format(message_list[i + 1].line, message_list[i + 1].msg))
                    elif len(messages) < self._number_of_messages - 1:
                        messages.append('[Line {}] {}'.format(message_list[i + 1].line, message_list[i + 1].msg))
                    message_list.pop(i + 1)

                msg_new = message_list[i].msg

                if len(messages) > 0:
                    msg_new = message_list[i].msg + '\n    ' + '\n    '.join(messages)

                obj_new = 'Number of occurrences: {}.'.format(count)

                if self._number_of_messages != 0 and self._number_of_messages < count:
                    obj_new = obj_new + ' First {} shown.'.format(self._number_of_messages)

                message_list[i] = message_list[i]._replace(msg=msg_new, obj=obj_new)
                i += 1

    _display = None
