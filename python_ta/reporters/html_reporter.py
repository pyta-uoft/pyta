import os
import webbrowser

from jinja2 import Environment, FileSystemLoader
from datetime import datetime

from .color_reporter import ColorReporter

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


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

    # Override this method
    def print_messages(self, level='all'):
        # Sort the messages.
        self.sort_messages()
        # Call these two just to fill snippet attribute of Messages
        # (and also to fix weird bad-whitespace thing):
        self._colour_messages_by_type(style=False)
        self._colour_messages_by_type(style=True)

        template = Environment(loader=FileSystemLoader(THIS_DIR)).get_template('templates/template.txt')
        output_path = THIS_DIR + '/templates/output.html'

        # Date/time (24 hour time) format:
        # Generated: ShortDay. ShortMonth. PaddedDay LongYear, Hour:Min:Sec
        dt = 'Generated: ' + str(datetime.now().
                                 strftime('%a. %b. %d %Y, %H:%M:%S'))
        with open(output_path, 'w') as f:
            f.write(template.render(date_time=dt,
                                    mod_name=self._module_name,
                                    code=self._sorted_error_messages,
                                    style=self._sorted_style_messages))
        print('Opening your report in a browser...')
        output_url = 'file:///{}/templates/output.html'.format(THIS_DIR)
        webbrowser.open(output_url)

    _display = None
