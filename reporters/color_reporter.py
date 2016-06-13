from pylint.reporters import BaseReporter

import sys
from colorama import Fore, Style
from colorama import init


class ColorReporter(BaseReporter):
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

        init(wrap=(sys.platform == "win32"))
        for msg in self._messages:
            if msg.msg_id.startswith('E'):
                # Error codes appear in red
                code = Fore.RED + Style.BRIGHT + msg.msg_id + Style.RESET_ALL
            else:
                code = Style.BRIGHT + msg.msg_id + Style.RESET_ALL
            print(code, '({})\n    {}'.format(msg.symbol, msg.msg))
