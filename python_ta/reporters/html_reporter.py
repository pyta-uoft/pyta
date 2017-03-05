import os

from jinja2 import Environment, FileSystemLoader

from .color_reporter import ColorReporter

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


class HTMLReporter(ColorReporter):
    # Override this method
    def print_messages(self, level='all'):
        # Sort the messages.
        self.sort_messages()

        template = Environment(loader=FileSystemLoader(THIS_DIR)).get_template('templates/template.txt')
        output_path = THIS_DIR + '/templates/output.html'

        with open(output_path, 'w') as f:
            f.write(template.render(code=self._sorted_error_messages, style=self._sorted_style_messages))
