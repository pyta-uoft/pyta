from reporters.plain_reporter import PlainReporter
from jinja2 import Environment


class HTMLReporter(PlainReporter):
    def __init__(self):
        super().__init__()

    # Override this method
    def print_message_ids(self):
        # Sort the messages.
        self._messages.sort(key=lambda s: s[0])

        #template = Environment(keep_trailing_newline=True, autoescape=False).from_string(HTML)
        template = Environment().get_template('template.txt')
        f = open('output.html', 'w')

        for msg in self._messages:
            code = msg.msg_id
            msg_new = msg.msg.replace('\n', '<br/>')
            msg = msg._replace(msg=msg_new)
            f = open('output.html', 'a')
            f.write(template.render(code=code,symbol=msg.symbol,obj=msg.obj,msg=msg.msg))
            print(template.render(code=code,symbol=msg.symbol,obj=msg.obj,msg=msg.msg))
        f.close()
