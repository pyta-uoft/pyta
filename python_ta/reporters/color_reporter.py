import sys

from colorama import Fore, Style, Back
from colorama import init

from .plain_reporter import PlainReporter


# One-size-fits-all type messages (symbols)
# simple = {"IO-function-not-allowed",
#           "forbidden-import",
#           "invalid-name",
#           "forbidden-global-variables",
#           "blacklisted-name",
#           "unneeded-not"}

# Messages that should be highlighted specially
special = {"missing-docstring",
           "trailing-newlines"}

# Messages without a source code line to highlight
no_hl = {"always-returning-in-a-loop",
         "too-many-nested-blocks"}
    # the "Invalid module name" subsection of "invalid-name" belongs here


class ColorReporter(PlainReporter):
    # Override this method to add instance variables
    def __init__(self, number_of_messages, source_lines=None, module_name=''):
        super().__init__(number_of_messages, source_lines, module_name)
        self._sorted_error_messages = {}
        self._sorted_style_messages = {}

    # Override this method
    def print_messages(self, level='all'):
        # Check if the OS currently running is Windows
        init(wrap=(sys.platform == 'win32'), strip=False)

        self.sort_messages()

        result = self._colourify(Fore.RED + Style.BRIGHT,
                                  '=== Code errors/forbidden usage '
                                  '(fix these right away!) ===\n')
        result += self._colour_messages_by_type(style=False)

        if level == 'all':
            result += '\n' + self._colourify(Fore.BLUE + Style.BRIGHT,
                                             '=== Style/convention errors '
                                             '(fix these before submission) ===\n')
            result += self._colour_messages_by_type(style=True)

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

    def _colour_messages_by_type(self, style=False):
        """
        Return string of properly formatted members of the messages dict
        (error or style) indicated by style.

        :param bool style: True iff messages is a dict of style messages
        :return: str
        """
        result = ""

        messages = (self._sorted_style_messages if style
                    else self._sorted_error_messages)

        for msg_id in messages:
            code = self._colourify((Fore.BLUE if style
                                    else Fore.RED) + Style.BRIGHT, msg_id)
            first_msg = messages[msg_id][0]
            result += code + ' ({})  {}\n'.format(first_msg.symbol,
                                                  first_msg.obj) + '\n'
            for i, msg in enumerate(messages[msg_id]):
                msg_text = msg.msg
                if msg.symbol == "bad-whitespace":  # fix Pylint inconsistency
                    msg_text = msg_text.partition('\n')[0]
                    messages[msg_id][i] = msg._replace(msg=msg_text)
                    msg = messages[msg_id][i]

                result += self._colourify(Style.BRIGHT,
                                          '   [Line {}] {}'.format(
                                              msg.line, msg.msg)) + '\n'

                try:
                    # Messages with code snippets
                    if not (msg.symbol in no_hl or
                            msg.msg.startswith("Invalid module") or msg.msg.startswith("Missing module docstring")):

                        if hasattr(msg, "node") and msg.node is not None:
                            start = msg.node.fromlineno
                            end = msg.node.end_lineno
                        else:
                            # Some message types don't have a node, including:
                            # - line-too-long
                            # - bad-whitespace
                            # - trailing-newlines
                            start = end = msg.line

                        # print('      ', msg.symbol, msg.node.lineno, msg.node.col_offset,
                        #       msg.node.end_lineno, msg.node.end_col_offset)

                        result += self._colourify(
                            Style.BRIGHT, '\n    Your Code Starts Here:\n')
                        result += '\n'

                        code_snippet = ""
                        if msg.symbol in special:
                            if msg.symbol == "trailing-newlines":
                                if start - 3 >= 0:
                                    code_snippet += self._add_line(
                                        msg, start - 3, 'c')
                                if start - 2 >= 0:
                                    code_snippet += self._add_line(
                                        msg, start - 2, 'c')
                                # Actual code line is empty, so just print number:
                                code_snippet += self._add_line(msg, start - 1, 'n')

                            elif msg.msg.startswith("Missing function docstring"):
                                code_snippet += self._add_line(
                                    msg, start - 1, 'e')
                                code_snippet += self._add_line(msg, start, '.')
                        else:
                            if end - start <= 3:  # add pre-context code (in grey)
                                if start - 3 >= 0:
                                    code_snippet += self._add_line(
                                        msg, start - 3, 'c')
                                if start - 2 >= 0:
                                    code_snippet += self._add_line(
                                        msg, start - 2, 'c')

                            code_snippet += self._add_line(msg, start - 1, 'e')
                            for line in range(start, end):
                                code_snippet += self._add_line(msg, line, 'o')

                            if end - start <= 3:  # add post-context
                                if end < len(self._source_lines):
                                    code_snippet += self._add_line(
                                        msg, end, 'c')
                                if end + 1 < len(self._source_lines):
                                    code_snippet += self._add_line(
                                        msg, end + 1, 'c')

                        result += code_snippet + '\n'
                        try:
                            messages[msg_id][i] = msg._replace(snippet=code_snippet)
                        except ValueError as e:
                            # raise ValueError("Non-NewMessage message has "
                            #                  "no 'snippet' attribute") from e
                            pass

                except AttributeError:
                    pass

                result += '\n'
        return result

    def _add_line(self, msg, n, linetype):
        """
        Format given source code line as specified and return as str.
        Use linetype='.' to elide line (with proper indentation).

        :param int n: index of line in self._source_lines to add
        :param str linetype: e/c/o/n/. for error/context/other/number-only/ellipsis
        :return: str
        """
        snippet = ""
        if n == -1:
            n = 0
        text = self._source_lines[n][:-1]
        # Pad line number with spaces to even out indent:
        number = self._colourify(Fore.LIGHTBLACK_EX, "{:>3}".format(n + 1))
        # UNCOMMENT TO IGNORE BLANK LINES:
        # if text.strip() == '':
        #     return

        if linetype == "e":  # (error)
            snippet += '    ' + self._colourify(Style.BRIGHT, number)
            if hasattr(msg, "node") and msg.node is not None:
                start_col = msg.node.col_offset
                end_col = msg.node.end_col_offset
            else:
                start_col = 0
                end_col = len(text)
            # if msg.symbol == "trailing-newlines":
            #     print(repr(text))
            snippet += '    ' + text[:start_col]
            snippet += self._colourify(Style.BRIGHT + Fore.BLACK + Back.CYAN,
                                       text[start_col:end_col])
            snippet += text[end_col:]

        elif linetype == "c":  # (context)
            snippet += '    ' + number
            snippet += '    ' + self._colourify(Fore.LIGHTBLACK_EX, text)

        elif linetype == "o":  # (other)
            snippet += '    ' + number
            snippet += '    ' + text

        elif linetype == "n":  # (number only)
            snippet += '    ' + self._colourify(
                Style.BRIGHT + Fore.BLACK + Back.CYAN, number)

        elif linetype == '.':  # (ellipsis)
            snippet += '    ' + number
            snippet += '    '
            spaces = len(text) - len(text.lstrip(' '))
            snippet += spaces * ' ' + '...'

        else:
            print("ERROR")

        snippet += '\n'

        return snippet

    @staticmethod
    def _colourify(colour, text):
        """
        Adds given ANSI colouring tokens to text as well as final colour reset.

        :param str colour: colorama ANSI code(s)
        :param str text: text to be coloured
        :return str
        """
        return colour + text + Style.RESET_ALL  # + Fore.RESET + Back.RESET
