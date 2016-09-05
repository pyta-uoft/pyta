import os

from jinja2 import Environment, FileSystemLoader

from .plain_reporter import PlainReporter

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


class HTMLReporter(PlainReporter):
    def __init__(self, number_of_messages):
        super().__init__(number_of_messages)

    # Override this method
    def print_message_ids(self):
        # Sort the messages.
        self.sort_messages()

        template = Environment(loader=FileSystemLoader(THIS_DIR)).get_template('templates/template.txt')

        with open('output.html', 'w') as f:
            for msg in self._error_messages:
                msg_new = msg.msg.replace('\r', '')
                msg_new = msg_new.replace('\n', '<br/>&emsp;&emsp;')
                i = self._error_messages.index(msg)
                self._error_messages[i] = msg._replace(msg=msg_new)

            for msg in self._style_messages:
                msg_new = msg.msg.replace('\r', '')
                msg_new = msg_new.replace('\n', '<br/>&emsp;&emsp;')
                i = self._style_messages.index(msg)
                self._style_messages[i] = msg._replace(msg=msg_new)

            f.write(template.render(messages=(self._error_messages + self._style_messages)))
