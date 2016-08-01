from reporters.plain_reporter import PlainReporter
from jinja2 import Environment, FileSystemLoader
import os

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


class HTMLReporter(PlainReporter):
    def __init__(self):
        super().__init__()

    # Override this method
    def print_message_ids(self):
        # Sort the messages.
        self.sort_messages()

        template = Environment(loader=FileSystemLoader(THIS_DIR)).get_template('templates/template.txt')

        with open('output.html', 'w') as f:
            for msg in self._messages:
                msg_new = msg.msg.replace('\r', '')
                msg_new = msg_new.replace('\n', '<br/>&emsp;&emsp;')
                i = self._messages.index(msg)
                self._messages[i] = msg._replace(msg=msg_new)

            f.write(template.render(messages=self._messages))
