import sys

from colorama import Fore, Style, Back
from colorama import init

from .plain_reporter import PlainReporter

# One-size-fits-all type messages (symbols)
simple = {"IO-function-not-allowed",
          "forbidden-import",
          "invalid-name",
          "forbidden-global-variables",
          "blacklisted-name"}

# Messages that could be in "simple", but would benefit
# from added pizazz using col_offsets
simplesque = {"unneeded-not"}

# Messages without a source code line to highlight
no_hl = {"missing-docstring"}
    # the "Invalid module name" subsection of "invalid-name" belongs here

# Other messages (need specialised colouring):
    # "always-returning-in-a-loop"


class ColorReporter(PlainReporter):
    # Override this method to add instance variables
    def __init__(self, number_of_messages, source_lines=None):
        super().__init__(number_of_messages, source_lines)
        self._sorted_error_messages = {}
        self._sorted_style_messages = {}

    # Override this method
    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)

        self.sort_messages()

        # TODO: compile string
        def print_messages_by_type(messages):
            for msg_id in messages:
                code = Fore.RED + Style.BRIGHT + msg_id + Style.RESET_ALL
                first_msg = messages[msg_id][0]
                print(code, '({})  {}\n'.format(first_msg.symbol, first_msg.obj))
                for msg in messages[msg_id]:
                    print(_colourify(Style.BRIGHT, '   [Line {}] {}'.format(msg.line, msg.msg)))
                    try:
                        start = msg.node.lineno     # TODO: change to fromlineno
                        end = msg.node.end_lineno
                        # print('   ', msg.node.lineno, msg.node.col_offset,
                        #      msg.node.end_lineno, msg.node.end_col_offset)
                        print(_colourify(Style.BRIGHT, '\n    Your Code Starts Here:\n'))
                        if end - start > 3:     # already enough context
                            if start != 0:
                                print(print('    ' + _colourify(Style.BRIGHT + Fore.LIGHTBLACK_EX, str(start)) +
                                      '    ' + _colourify(Style.BRIGHT + Fore.RED,
                                                          self._source_lines[start - 1])))
                                for line in range(start, end):
                                    print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(line + 1)) +
                                          '    ' + self._source_lines[line])
                            else:
                                print(print('    ' + _colourify(Style.BRIGHT + Fore.LIGHTBLACK_EX,
                                                                str(start + 1)) +
                                      '    ' + _colourify(Style.BRIGHT + Fore.YELLOW + Back.RED,
                                                          self._source_lines[start])))
                                for line in range(start + 1, end):
                                    print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(line + 1)) +
                                          '    ' + self._source_lines[line])
                        else:   # add surrounding code for context (in grey)
                            if start - 2 > 0:
                                print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(start - 2) +
                                      '    ' + self._source_lines[start - 3]))
                            if start - 1 > 0:
                                print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(start - 1) +
                                      '    ' + self._source_lines[start - 2]))
                            if start > 0:
                                print('    ' + _colourify(Style.BRIGHT + Fore.LIGHTBLACK_EX, str(start)) +
                                      '    ' + _colourify(Style.BRIGHT + Fore.YELLOW + Back.RED,
                                                          self._source_lines[start - 1][:-1]))
                                for line in range(start, end):
                                    print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(line + 1)) +
                                          '    ' + self._source_lines[line][:-1])
                            else:
                                print(print('    ' + _colourify(Style.BRIGHT + Fore.LIGHTBLACK_EX,
                                                                str(start + 1)) +
                                            '    ' + _colourify(Style.BRIGHT + Fore.YELLOW + Back.RED,
                                                                self._source_lines[start])))
                                for line in range(start + 1, end):
                                    print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(line + 1)) +
                                          '    ' + self._source_lines[line])
                            if end + 1 < len(self._source_lines):
                                print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(end + 1) +
                                      '    ' + self._source_lines[end]))
                            if end + 2 < len(self._source_lines):
                                print('    ' + _colourify(Fore.LIGHTBLACK_EX, str(end + 2) +
                                      '    ' + self._source_lines[end + 1]))

                    except AttributeError:
                        pass
                    print('\n')

        print(_colourify(Style.BRIGHT,
                         '=== Code errors/forbidden usage (fix these right away!) ==='))
        print_messages_by_type(self._sorted_error_messages)

        if level == 'all':
            print(_colourify(Style.BRIGHT, '=== Style/convention errors (fix these before submission) ==='))
            print_messages_by_type(self._sorted_style_messages)

    # Override this method
    def sort_messages(self):
        # Sort the messages by their type
        def sort_messages_by_type(messages):
            messages.sort(key=lambda s: s[0])
            sorted_messages = {}
            # Count the number of occurrences and sort the msgs according to their id's
            i = 0
            while i < len(messages):
                current_id = messages[i].msg_id
                count = 1
                sorted_messages[current_id] = [messages[i]]
                while i + 1 < len(messages) and messages[i + 1].msg_id == current_id:
                    count += 1
                    sorted_messages[current_id].append(messages[i + 1])
                    i += 1

                obj_new = 'Number of occurrences: {}.'.format(count)

                if self._number_of_messages != 0 and self._number_of_messages < count:
                    obj_new += ' First {} shown.'.format(self._number_of_messages)

                sorted_messages[current_id][0] = sorted_messages[current_id][0]._replace(obj=obj_new)
                i += 1
            return sorted_messages

        self._sorted_error_messages = sort_messages_by_type(self._error_messages)
        self._sorted_style_messages = sort_messages_by_type(self._style_messages)

    _display = None   # because PyCharm is annoying about this


def _colourify(colour, text):
    """
    Adds given ANSI colouring tokens to text as well as final colour reset.

    :param str colour: colorama ANSI code(s)
    :param str text: text to be coloured
    :return str
    """
    return colour + text + Fore.RESET + Back.RESET + Style.RESET_ALL
