import sys

from colorama import Fore, Style, Back
from colorama import init

from .plain_reporter import PlainReporter


# One-size-fits-all type messages (symbols)
simple = {"IO-function-not-allowed",
          "forbidden-import",
          "invalid-name",
          "forbidden-global-variables",
          "blacklisted-name",
          "unneeded-not"}

# Messages without a source code line to highlight or
# that should be highlighted specially
special = {"missing-docstring",
           "always-returning-in-a-loop",
           "too-many-nested-blocks"}
    # the "Invalid module name" subsection of "invalid-name" belongs here


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

        result = ""

        def print_messages_by_type(messages, style=False):
            """
            Add properly formatted members of messages to result.

            :param dict messages: dictionary of message id: Message object
            :param bool style: True iff messages is a dict of style messages
            :return: None
            """
            nonlocal result

            # TODO: Is a triply nested function overkill? Switch to method?
            def add_line(n, linetype):
                """
                Format given source code line as specified and add to result.
                Use linetype='.' to elide line (with proper indentation).

                :param int n: index of line in self._source_lines to add
                :param str linetype: e/c/o/. for error/context/other/ellipsis
                :return: None
                """
                nonlocal result
                if n == -1:
                    n = 0
                text = self._source_lines[n][:-1]
                # UNCOMMENT TO IGNORE BLANK LINES:
                # if text.strip() == '':
                #     return

                if linetype == "e":    # (error)
                    result += '    ' + \
                              _colourify(Style.BRIGHT + Fore.LIGHTBLACK_EX,
                                         str(n + 1))
                    start_col = msg.node.col_offset
                    end_col = msg.node.end_col_offset
                    result += '    ' + text[:start_col]
                    result += _colourify(Style.BRIGHT + Fore.BLACK + Back.CYAN,
                                         text[start_col:end_col])
                    result += text[end_col:]

                elif linetype == "c":  # (context)
                    result += '    ' + _colourify(Fore.LIGHTBLACK_EX, str(n + 1))
                    result += '    ' + _colourify(Fore.LIGHTBLACK_EX, text)

                elif linetype == "o":  # (other)
                    result += '    ' + _colourify(Fore.LIGHTBLACK_EX, str(n + 1))
                    result += '    ' + text

                elif linetype == '.':  # (ellipsis)
                    result += '    ' + _colourify(Fore.LIGHTBLACK_EX, str(n + 1))
                    result += '    '
                    spaces = len(text) - len(text.lstrip(' '))
                    result += spaces * ' ' + '...'

                else:
                    print("ERROR")

                result += '\n'

            for msg_id in messages:
                code = _colourify((Fore.BLUE if style
                                   else Fore.RED) + Style.BRIGHT, msg_id)
                first_msg = messages[msg_id][0]
                result += code + ' ({})  {}\n'.format(first_msg.symbol,
                                                      first_msg.obj) + '\n'
                for msg in messages[msg_id]:
                    result += _colourify(Style.BRIGHT, '   [Line {}] {}'.format(
                        msg.line, msg.msg)) + '\n'

                    try:
                        start = msg.node.fromlineno
                        end = msg.node.end_lineno
                        # print('      ', msg.symbol, msg.node.lineno, msg.node.col_offset,
                        #       msg.node.end_lineno, msg.node.end_col_offset)

                        # Regular/simple messages
                        if not (msg.symbol in special or
                                msg.msg.startswith("Invalid module")):
                            result += _colourify(Style.BRIGHT,
                                                 '\n    Your Code Starts Here:\n') + '\n'

                            if end - start <= 3:  # add pre-context code (in grey)
                                if start - 3 >= 0:
                                    add_line(start - 3, 'c')
                                if start - 2 >= 0:
                                    add_line(start - 2, 'c')

                            add_line(start - 1, 'e')
                            for line in range(start, end):
                                add_line(line, 'o')

                            if end - start <= 3:  # add post-context
                                if end < len(self._source_lines):
                                    add_line(end, 'c')
                                if end + 1 < len(self._source_lines):
                                    add_line(end + 1, 'c')

                        # Special messages (no code or special highlight)
                        else:
                            if msg.msg.startswith("Missing function docstring"):
                                add_line(start - 1, 'e')
                                add_line(start, '.')

                            if msg.symbol == "too-many-nested-blocks":
                                pass

                            if msg.symbol == "always-returning-in-a-loop":
                                pass

                    except AttributeError:
                        # print('      PROBLEM: ', msg.symbol)
                        pass
                    result += '\n'

        result += _colourify(Fore.RED + Style.BRIGHT,
                             '=== Code errors/forbidden usage '
                             '(fix these right away!) ===\n')
        print_messages_by_type(self._sorted_error_messages)

        if level == 'all':
            result += '\n' + _colourify(Fore.BLUE + Style.BRIGHT,
                                        '=== Style/convention errors '
                                        '(fix these before submission) ===\n')
            print_messages_by_type(self._sorted_style_messages, True)

        print(result)

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
    return colour + text + Style.RESET_ALL  # + Fore.RESET + Back.RESET
