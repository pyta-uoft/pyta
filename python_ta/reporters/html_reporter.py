import os

from jinja2 import Environment, FileSystemLoader

from .color_reporter import ColorReporter

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
_SPACES = '&nbsp;&nbsp;&nbsp;&nbsp;'  # 4 HTML non-breaking spaces


class HTMLReporter(ColorReporter):
    # Override this method
    def print_messages(self, level='all'):
        # Sort the messages.
        self.sort_messages()
        # Call these two just to fill snippet attribute of Messages:
        self._colour_messages_by_type(style=False)
        self._colour_messages_by_type(style=True)

        template = Environment(loader=FileSystemLoader(THIS_DIR)).get_template('templates/template.txt')
        output_path = THIS_DIR + '/templates/output.html'

        with open(output_path, 'w') as f:
            f.write(template.render(code=self._sorted_error_messages,
                                    style=self._sorted_style_messages))

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
        number = "{:>3}".format(n + 1)
        # UNCOMMENT TO IGNORE BLANK LINES:
        # if text.strip() == '':
        #     return

        if linetype == "e":  # (error)
            snippet += _SPACES + self._colourify("gbold", number)
            if hasattr(msg, "node") and msg.node is not None:
                start_col = msg.node.col_offset
                end_col = msg.node.end_col_offset
            else:
                start_col = 0
                end_col = len(text) - 1
            # if msg.symbol == "trailing-newlines":
            #     print(repr(text))
            snippet += _SPACES + self._colourify("black", text[:start_col])
            # Because highlight works on the col_offsets of a particular line, the &nbsp spacing in the colourify method
            # wouldn't work. So treat this case separately.
            snippet += self._colourify("highlight",     # bold, black on cyan
                                       text[start_col:end_col])
            snippet += self._colourify("black", text[end_col:])

        elif linetype == "c":  # (context)
            snippet += _SPACES + self._colourify("grey", number)
            snippet += _SPACES + self._colourify("grey", text)

        elif linetype == "o":  # (other)
            snippet += _SPACES + self._colourify("grey", number)
            snippet += _SPACES + text

        elif linetype == "n":  # (number only)
            snippet += _SPACES + self._colourify("highlight", number)

        elif linetype == '.':  # (ellipsis)
            snippet += _SPACES + self._colourify("grey", number)
            snippet += _SPACES
            space_count = len(text) - len(text.lstrip(' '))
            snippet += space_count * '&nbsp;' + '...'

        else:
            print("ERROR")

        snippet += '<br/>'
        print(snippet)
        return snippet

    @staticmethod
    def _colourify(colour_class, text):
        space_count = len(text) - len(text.lstrip(' '))
        text = text.lstrip()
        if (colour_class == "highlight") and (not text.isdigit()):
            return '<span class="' + colour_class + '">' + text + '</span>'
        else:
            return '<span class="' + colour_class + '">' + (space_count * '&nbsp;') + text + '</span>'
