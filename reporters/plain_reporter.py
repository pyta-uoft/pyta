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
        # Check if the OS currently running is Windows

        for msg in self._messages:
            if msg.msg_id.startswith('E'):
                # Error codes appear in red
                # code = '\033[1;31m' + msg.msg_id + '\033[0m:'
                code = msg.msg_id
            else:
                # code = '\033[1m' + msg.msg_id + '\033[0m:'
                code = msg.msg_id
            print(code, '({})\n    {}'.format(msg.symbol, msg.msg))
