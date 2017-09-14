import os
import webbrowser
from collections import namedtuple

from jinja2 import Environment, FileSystemLoader
from datetime import datetime
from base64 import b64encode

from .color_reporter import ColorReporter

TEMPLATES_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates')

class HTMLReporter(ColorReporter):
    _SPACE = '&nbsp;'
    _BREAK = '<br/>'
    _COLOURING = {'black': '<span class="black">',
                  'bold': '<span>',
                  'code-heading': '<span>',
                  'style-heading': '<span>',
                  'code-name': '<span>',
                  'style-name': '<span>',
                  'highlight': '<span class="highlight">',
                  'grey': '<span class="grey">',
                  'gbold': '<span class="gbold">',
                  'reset': '</span>'}
    code_err_title = 'Code Errors or Forbidden Usage (fix: high priority)'
    style_err_title = 'Style or Convention Errors (fix: before submission)'

    def __init__(self, source_lines=None, module_name=''):
        super().__init__(source_lines, module_name)
        self.messages_by_file = []

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
                               code=dict(self._sorted_error_messages),
                               style=dict(self._sorted_style_messages))
        self.messages_by_file.append(append_set)

    def output_blob(self):
        """Output to the template after all messages."""
        template_f = self.linter.config.pyta_template_file
        template = Environment(loader=FileSystemLoader(TEMPLATES_DIR)).get_template(template_f)

        # Embed resources so the output html can go anywhere, independent of assets.
        # with open(os.path.join(TEMPLATES_DIR, 'pyta_logo_markdown.png'), 'rb+') as image_file:
        #     # Encode img binary to base64 (+33% size), decode to remove the "b'"
        #     pyta_logo_base64_encoded = b64encode(image_file.read()).decode()

        # Date/time (24 hour time) format:
        # Generated: ShortDay. ShortMonth. PaddedDay LongYear, Hour:Min:Sec
        dt = str(datetime.now().strftime('%a. %b. %d %Y, %I:%M:%S %p'))
        output_path = os.path.join(os.getcwd(), self.linter.config.pyta_output_file)
        with open(output_path, 'w') as f:
            f.write(template.render(date_time=dt,
                                    # pyta_logo=pyta_logo_base64_encoded,
                                    reporter=self))
        print('Opening your report in a browser...')
        output_url = 'file:///{}'.format(output_path)
        webbrowser.open(output_url)

    _display = None
