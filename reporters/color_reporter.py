from reporters.plain_reporter import PlainReporter

import sys
from colorama import Fore, Style
from colorama import init


class ColorReporter(PlainReporter):
    def __init__(self):
        super().__init__()

    # Override this method
    def print_message_ids(self):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'))

        # Sort the messages by their type.
        self._messages.sort(key=lambda s: s[0])

        for msg in self._messages:
            if msg.msg_id.startswith('E'):
                # Error codes appear in red
                code = Fore.RED + Style.BRIGHT + msg.msg_id + Style.RESET_ALL
            else:
                code = Style.BRIGHT + msg.msg_id + Style.RESET_ALL
            print(code, '({})\n    [Line {}] {}'.format(msg.symbol, msg.line, msg.msg))
