from pylint.reporters import BaseReporter


class PlainReporter(BaseReporter):
    def __init__(self):
        super().__init__(self)
        self._messages = []

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        self._messages.append(msg)

    def print_message_ids(self):
        # Sort the messages by their type.
        self._messages.sort(key=lambda s: s[0])

        for msg in self._messages:
            code = msg.msg_id
            print(code, '({})\n    {}'.format(msg.symbol, msg.msg))
