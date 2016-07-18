from pylint.reporters import BaseReporter


class PlainReporter(BaseReporter):
    def __init__(self, number):
        super().__init__(self)
        self._messages = []
        self._number = number

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        self._messages.append(msg)

    def print_message_ids(self):
        # Sort the messages.
        self.sort_messages()
        for msg in self._messages:
            code = msg.msg_id
            print(code, '({}) {}\n    {}'.format(msg.symbol, msg.obj, msg.msg))

    def sort_messages(self):
        # Sort the messages by their type.
        self._messages.sort(key=lambda s: s[0])

        i = 0
        while i < len(self._messages):
            current_id = self._messages[i].msg_id
            count = 1
            messages = []
            while i + 1 < len(self._messages) and self._messages[i + 1].msg_id == current_id:
                count += 1
                if self._number == 0:
                    messages.append(self._messages[i + 1].msg)
                elif len(messages) < self._number - 1:
                    messages.append(self._messages[i + 1].msg)
                self._messages.pop(i + 1)

            msg_new = self._messages[i].msg

            if len(messages) > 0:
                msg_new = self._messages[i].msg + '\n    ' + '\n    '.join(messages)

            obj_new = 'This error occurs at ' + str(count) + ' places:'

            if self._number != 0 and self._number < count:
                obj_new = 'This error occurs at ' + str(count) + ' places. Only first ' + str(self._number) + ' errors shown:'

            self._messages[i] = self._messages[i]._replace(msg=msg_new, obj=obj_new)
            i += 1
