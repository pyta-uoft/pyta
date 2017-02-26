import sys

from colorama import Fore, Style
from colorama import init

from .plain_reporter import PlainReporter


class ColorReporter(PlainReporter):
    sorted_error_message = {}
    sorted_style_message = {}

    # Override this method
    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)

        self.sort_messages()

        print(Style.BRIGHT + '=== Code errors/forbidden usage (fix these right away!) ===' + Style.RESET_ALL)
        for msg_id in ColorReporter.sorted_error_message:
            code = Fore.RED + Style.BRIGHT + msg_id + Style.RESET_ALL
            first_msg = ColorReporter.sorted_error_message[msg_id][0]
            print(code, '({})  {}\n'.format(first_msg.symbol, first_msg.obj))
            for msg in ColorReporter.sorted_error_message[msg_id]:
                print(Style.BRIGHT + '   [Line {}] {}'.format(msg.line, msg.msg) + Style.RESET_ALL)
                try:
                    #print('   ', msg.node.lineno, msg.node.col_offset,
                    #      msg.node.end_lineno, msg.node.end_col_offset)
                    print(Style.BRIGHT + '\n    Your Code Starts Here:\n' + Style.RESET_ALL)
                    if msg.node.lineno != 0:
                        print('    ' + Fore.LIGHTBLACK_EX + str(msg.node.lineno) + Style.RESET_ALL +
                              '    ' + Fore.RED + self._source_lines[msg.node.lineno - 1] + Style.RESET_ALL)
                        for line in range(msg.node.lineno, msg.node.end_lineno):
                            print('    ' + Fore.LIGHTBLACK_EX + str(line + 1) + Style.RESET_ALL +
                                  '    ' + self._source_lines[line])
                    else:
                        print('    ' + Fore.LIGHTBLACK_EX + str(msg.node.lineno + 1) + Style.RESET_ALL +
                              '    ' + Fore.RED + self._source_lines[msg.node.lineno] + Style.RESET_ALL)
                        for line in range(msg.node.lineno + 1, msg.node.end_lineno):
                            print('    ' + Fore.LIGHTBLACK_EX + str(line + 1) + Style.RESET_ALL +
                                  '    ' + self._source_lines[line])
                except AttributeError:
                    pass
                print('\n')

        if level == 'all':
            print(Style.BRIGHT + '=== Style/convention errors (fix these before submission) ===' + Style.RESET_ALL)
            for msg_id in ColorReporter.sorted_style_message:
                code = Style.BRIGHT + msg_id + Style.RESET_ALL
                first_msg = ColorReporter.sorted_style_message[msg_id][0]
                print(code, '({})  {}\n'.format(first_msg.symbol, first_msg.obj))
                for msg in ColorReporter.sorted_style_message[msg_id]:
                    print(Style.BRIGHT + '   [Line {}] {}'.format(msg.line, msg.msg) + Style.RESET_ALL)
                    try:
                        #print('   ', msg.node.lineno, msg.node.col_offset,
                        #      msg.node.end_lineno, msg.node.end_col_offset)
                        print(Style.BRIGHT + '\n    Your Code Starts Here:\n' + Style.RESET_ALL)
                        if msg.node.lineno != 0:
                            print('    ' + Fore.LIGHTBLACK_EX + str(msg.node.lineno) + Style.RESET_ALL +
                                  '    ' + Fore.RED + self._source_lines[msg.node.lineno - 1] + Style.RESET_ALL)
                            for line in range(msg.node.lineno, msg.node.end_lineno):
                                print('    ' + Fore.LIGHTBLACK_EX + str(line + 1) + Style.RESET_ALL +
                                      '    ' + self._source_lines[line])
                        else:
                            print('    ' + Fore.LIGHTBLACK_EX + str(msg.node.lineno + 1) + Style.RESET_ALL +
                                  '    ' + Fore.RED + self._source_lines[msg.node.lineno] + Style.RESET_ALL)
                            for line in range(msg.node.lineno + 1, msg.node.end_lineno):
                                print('    ' + Fore.LIGHTBLACK_EX + str(line + 1) + Style.RESET_ALL +
                                      '    ' + self._source_lines[line])
                    except AttributeError:
                        pass
                    print('\n')
        ColorReporter.sorted_error_message.clear()
        ColorReporter.sorted_style_message.clear()

    # Override this method
    def sort_messages(self):
        # Sort the messages by their type
        self._error_messages.sort(key=lambda s: s[0])
        # Count the number of occurrences and sort the msgs according to their id's
        i = 0
        while i < len(self._error_messages):
            current_id = self._error_messages[i].msg_id
            count = 1
            ColorReporter.sorted_error_message[current_id] = [self._error_messages[i]]
            while i + 1 < len(self._error_messages) and self._error_messages[i + 1].msg_id == current_id:
                count += 1
                ColorReporter.sorted_error_message[current_id].append(self._error_messages[i + 1])
                i += 1

            obj_new = 'Number of occurrences: {}.'.format(count)

            if self._number_of_messages != 0 and self._number_of_messages < count:
                obj_new += ' First {} shown.'.format(self._number_of_messages)

            ColorReporter.sorted_error_message[current_id][0] = ColorReporter.sorted_error_message[current_id][0]._replace(obj=obj_new)
            i += 1

        j = 0
        self._style_messages.sort(key=lambda s: s[0])
        # Count the number of occurrences and sort the msgs according to their id's
        while j < len(self._style_messages):
            current_id = self._style_messages[j].msg_id
            count = 1
            ColorReporter.sorted_style_message[current_id] = [self._style_messages[j]]
            while j + 1 < len(self._style_messages) and self._style_messages[j + 1].msg_id == current_id:
                count += 1
                ColorReporter.sorted_style_message[current_id].append(self._style_messages[j + 1])
                j += 1

            obj_new = 'Number of occurrences: {}.'.format(count)

            if self._number_of_messages != 0 and self._number_of_messages < count:
                obj_new += ' First {} shown.'.format(self._number_of_messages)

            ColorReporter.sorted_style_message[current_id][0] = ColorReporter.sorted_style_message[current_id][0]._replace(obj=obj_new)
            j += 1
