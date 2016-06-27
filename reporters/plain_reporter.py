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
            print(code, '({})\n    {}'.format(msg.symbol, msg.msg))

    def sort_messages(self):
        # Sort the messages by their type.
        self._messages.sort(key=lambda s: s[0])

        i = 0
        while i < len(self._messages):
            current_id = self._messages[i].msg_id
            count = 1
            messages = ''
            msg_count = 1
            while i+1 < len(self._messages) and self._messages[i+1].msg_id == current_id:
                count += 1
                if msg_count <= 5:
                    messages += '\n    ' + self._messages[i+1].msg
                    msg_count += 1
                self._messages.pop(i+1)

            msg = self._messages[i].msg

            if count > 1:
                msg = 'This error occurs at '+ str(count) + ' places:\n    ' + self._messages[i].msg + messages
                #temp = self._messages[i].__setattr__(self._messages[i].msg, 'hello')
            #elif count == 1:
            #    msg = self._messages[i].msg + 'This error occurs at 1 place.'

            msgid = self._messages[i].msg_id
            symbol = self._messages[i].symbol
            confidence = self._messages[i].confidence
            abspath = self._messages[i].abspath
            path = self._messages[i].path
            module = self._messages[i].module
            obj = self._messages[i].obj
            line = self._messages[i].line
            column = self._messages[i].column
            self._messages[i] = Message(msgid, symbol, (abspath, path,
                                                            module, obj, line,
                                                            column), msg,
                                            confidence)

            #Message(msgid, symbol='forbidden-global-variables', msg="Global variables should not be used in CSC108/CSC148 - you used the keyword 'global' on line 7", C='E', category='error', confidence)

            count = 0
            i += 1
