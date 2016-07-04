from pylint.reporters import BaseReporter
from pylint.utils import Message


class PlainReporter(BaseReporter):
    def __init__(self):
        super().__init__(self)
        self._messages = []

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        self._messages.append(msg)

    def print_message_ids(self):
        # Sort the messages by their type.
        #self._messages.sort(key=lambda s: s[0])
        self.sort_messages()
        for msg in self._messages:
            code = msg.msg_id
            #print(code, '({})\n    {}'.format(msg.symbol, msg.msg))
            print(code, '({}) {}\n    {}'.format(msg.symbol, msg.obj, msg.msg))
            # print(msg)

    def sort_messages(self):
        # Sort the messages by their type.
        self._messages.sort(key=lambda s: s[0])

        i = 0
        while i < len(self._messages):
            current_id = self._messages[i].msg_id
            count = 1
            messages = []
            while i + 1 < len(self._messages) and self._messages[i + 1].msg_id == current_id:
                count += 1
                if len(messages) <= 5:
                    messages.append(self._messages[i+1].msg)
                self._messages.pop(i+1)

            msg_new = self._messages[i].msg

            if len(messages) > 0:
                temp = '\n    ' + '\n    '.join(messages)
                msg_new = self._messages[i].msg + temp

            obj_new = 'This error occurs at ' + str(count) + ' places:'
            # msgid = self._messages[i].msg_id
            # symbol = self._messages[i].symbol
            # confidence = self._messages[i].confidence
            # abspath = self._messages[i].abspath
            # path = self._messages[i].path
            # module = self._messages[i].module
            # obj = self._messages[i].obj
            # line = self._messages[i].line
            # column = self._messages[i].column
            # self._messages[i] = Message(msgid, symbol, (abspath, path,
            #                                                 module, obj, line,
            #                                                 column), msg,
            #                                 confidence)
            self._messages[i] = self._messages[i]._replace(msg=msg_new)
            self._messages[i] = self._messages[i]._replace(obj=obj_new)
            i += 1
