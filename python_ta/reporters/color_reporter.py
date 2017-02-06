import sys

from colorama import Fore, Style
from colorama import init

from .plain_reporter import PlainReporter


class ColorReporter(PlainReporter):
    # Override this method
    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)

        self.sort_messages()

        print(Style.BRIGHT + '=== Code errors/forbidden usage (fix these right away!) ===' + Style.RESET_ALL)
        for msg in self._error_messages:
            code = Fore.RED + Style.BRIGHT + msg.msg_id + Style.RESET_ALL
            print(code, '({})  {}\n    [Line {}] {}'.format(msg.symbol, msg.obj, msg.line, msg.msg))

        if level == 'all':
            print('\n')
            print(Style.BRIGHT + '=== Style/convention errors (fix these before submission) ===' + Style.RESET_ALL)
            for msg in self._style_messages:
                code = Style.BRIGHT + msg.msg_id + Style.RESET_ALL
                print(code, '({})  {}\n    [Line {}] {}'.format(msg.symbol, msg.obj, msg.line, msg.msg))
                # print('   ', msg.node.lineno, msg.node.col_offset, msg.node.end_lineno, msg.node.end_col_offset)
                print('   ', '\n'.join(self._source_lines[msg.node.lineno - 1:msg.node.end_lineno]))