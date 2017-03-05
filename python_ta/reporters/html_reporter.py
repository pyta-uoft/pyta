import os

from jinja2 import Environment, FileSystemLoader

from .plain_reporter import PlainReporter

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


class HTMLReporter(PlainReporter):
    # Override this method
    def print_messages(self, level='all'):
        # Sort the messages.
        self.sort_messages()

        template = Environment(loader=FileSystemLoader(THIS_DIR)).get_template('templates/template.txt')
        output_path = THIS_DIR + '/templates/outputt.html'

        with open(output_path, 'w') as f:
            f.write(template.render(error=(self._sorted_error_messages), style=(self._sorted_style_messages)))

    def sort_messages(self):
        # Sort the messages by their type
        def sort_messages_by_type(messages):
            messages.sort(key=lambda s: s[0])
            sorted_messages = {}
            # Count the number of occurrences and sort the msgs according to their id's
            i = 0
            while i < len(messages):
                current_id = messages[i].msg_id
                count = 1
                sorted_messages[current_id] = [messages[i]]
                while i + 1 < len(messages) and messages[i + 1].msg_id == current_id:
                    count += 1
                    sorted_messages[current_id].append(messages[i + 1])
                    i += 1

                obj_new = 'Number of occurrences: {}.'.format(count)

                if self._number_of_messages != 0 and self._number_of_messages < count:
                    obj_new += ' First {} shown.'.format(self._number_of_messages)

                sorted_messages[current_id][0] = sorted_messages[current_id][0]._replace(obj=obj_new)
                i += 1
            return sorted_messages

        self._sorted_error_messages = sort_messages_by_type(self._error_messages)
        self._sorted_style_messages = sort_messages_by_type(self._style_messages)
