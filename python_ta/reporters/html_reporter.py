import os
import webbrowser
from collections import defaultdict, namedtuple
from http.server import HTTPServer, BaseHTTPRequestHandler

from jinja2 import Environment, FileSystemLoader
from datetime import datetime
from base64 import b64encode

from pygments import highlight
from pygments.lexers import PythonLexer
from pygments.formatters import HtmlFormatter

from .color_reporter import ColorReporter

TEMPLATES_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates')


class HTMLReporter(ColorReporter):
    _COLOURING = {'black': '<span class="black">',
                  'black-line': '<span class="black line-num">',
                  'bold': '<span>',
                  'code-heading': '<span>',
                  'style-heading': '<span>',
                  'code-name': '<span>',
                  'style-name': '<span>',
                  'highlight': '<span class="highlight-pyta">',
                  'grey': '<span class="grey">',
                  'grey-line': '<span class="grey line-num">',
                  'gbold': '<span class="gbold">',
                  'gbold-line': '<span class="gbold line-num">',
                  'reset': '</span>'}
    code_err_title = 'Code Errors or Forbidden Usage (fix: high priority)'
    style_err_title = 'Style or Convention Errors (fix: before submission)'

    def __init__(self, source_lines=None, module_name=''):
        super().__init__(source_lines, module_name)
        self.messages_by_file = []

    def _messages_shown(self, sorted_messages):
        """Trim the amount of messages according to the default number.
        Add information about the number of occurrences vs number shown."""
        MessageSet = namedtuple('MessageSet', 'shown occurrences messages')
        ret_sorted = defaultdict()
        for message_key in sorted_messages:
            message_list = []
            for message_tuple_i in sorted_messages[message_key]:
                # Limit the number of messages shown
                if len(message_list) < self.linter.config.pyta_number_of_messages:
                    message_list.append(message_tuple_i)
            ret_sorted[message_key] = MessageSet(shown=len(message_list),
                                                 occurrences=len(sorted_messages[message_key]),
                                                 messages=message_list)
        return dict(ret_sorted)

    # Override this method
    def print_messages(self, level='all'):
        # Sort the messages.
        self.sort_messages()
        # Call these two just to fill snippet attribute of Messages
        # (and also to fix weird bad-whitespace thing):
        self._colour_messages_by_type(style=False)
        self._colour_messages_by_type(style=True)

        MessageSet = namedtuple('MessageSet', 'filename code style')
        append_set = MessageSet(filename=self.filename_to_display(self.current_file_linted),
                                code=self._messages_shown(self._sorted_error_messages),
                                style=self._messages_shown(self._sorted_style_messages))
        self.messages_by_file.append(append_set)

    def output_blob(self):
        """Output to the template after all messages."""
        if self.current_file_linted is None:
            # There were no files checked.
            print('[ERROR]: No files were checked.')
            return

        template_f = self.linter.config.pyta_template_file
        template = Environment(loader=FileSystemLoader(TEMPLATES_DIR)).get_template(template_f)

        # Embed resources so the output html can go anywhere, independent of assets.
        # with open(os.path.join(TEMPLATES_DIR, 'pyta_logo_markdown.png'), 'rb+') as image_file:
        #     # Encode img binary to base64 (+33% size), decode to remove the "b'"
        #     pyta_logo_base64_encoded = b64encode(image_file.read()).decode()

        # Date/time (24 hour time) format:
        # Generated: ShortDay. ShortMonth. PaddedDay LongYear, Hour:Min:Sec
        dt = str(datetime.now().strftime('%a. %b. %d %Y, %I:%M:%S %p'))

        # Render the jinja template
        rendered_template = template.render(date_time=dt, reporter=self)

        # If a filepath was specified, write to the file
        if self._output_filepath:
            self._write_html_to_file(rendered_template)
        else:
            self._open_html_in_browser(rendered_template.encode('utf8'))

    def _write_html_to_file(self, rendered_template):
        """ Write the html file to the specified output path. """
        output_path = os.path.join(os.getcwd(), self.linter.config.pyta_output_file)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(rendered_template)

    def _open_html_in_browser(self, html, new=0, autoraise=True):
        """
        Display html in a web browser without creating a temp file.
        Instantiates a trivial http server and uses the webbrowser module to
        open a URL to retrieve html from that server.

        Modified from: https://github.com/plotly/plotly.py/blob/master/packages/python/plotly/plotly/io/_base_renderers.py#L655
        """

        class OneShotRequestHandler(BaseHTTPRequestHandler):
            def do_GET(self):
                self.send_response(200)
                self.send_header("Content-type", "text/html")
                self.end_headers()

                buffer_size = 1024 * 1024
                for i in range(0, len(html), buffer_size):
                    self.wfile.write(html[i: i + buffer_size])

        server = HTTPServer(('127.0.0.1', 0), OneShotRequestHandler)
        webbrowser.open(f"http://127.0.0.1:{server.server_port}", new=new, autoraise=autoraise)
        server.handle_request()

    @classmethod
    def _vendor_wrap(self, colour_class, text):
        """Override in reporters that wrap snippet lines in vendor styles, e.g. pygments."""
        if '-line' not in colour_class:
            text = highlight(text, PythonLexer(),
                             HtmlFormatter(nowrap=True, lineseparator='', classprefix='pygments-'))
        return text

    _display = None
