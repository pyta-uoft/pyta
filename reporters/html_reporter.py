from reporters.plain_reporter import PlainReporter
from jinja2 import Environment

HTML = '''<html>
<head>
<title>{{ title }}</title>
</head>
<body>
    <p>{{ code }} ({{symbol}}) {{obj}}</p>
    <p>    {{msg}}</p>

</body>
</html>'''


class HTMLReporter(PlainReporter):
    def __init__(self):
        super().__init__()

    # Override this method
    def print_message_ids(self):
        # Sort the messages.
        self.sort_messages()

        #template = Template(u'{{ code }} ({{symbol}}) {{obj}}\n    {{msg}}')
        template = Environment(keep_trailing_newline=True, autoescape=False).from_string(HTML)

        for msg in self._messages:
            code = msg.msg_id

            msg_new = msg.msg.replace('\r\n', '<br/>')
            msg = msg._replace(msg=msg_new)
            print(template.render(code=code,symbol=msg.symbol,obj=msg.obj,msg=msg.msg))
