import sys
import json
# from colorama import Fore, Style, Back, init
from collections import defaultdict
from .plain_reporter import PlainReporter


class PositionReporter(PlainReporter):
    def __init__(self, source_lines=None, module_name=''):
        super().__init__(source_lines, module_name)
        self._output = {
            'total_genre_errors': 0,
            'total_genre_styles': 0,
            'total_results': 0,
            'results': []
        }

    def build_result(self, sorted_messages):
        """Build a dict of message data for errors or styles, based on a
        particular message id.
        """
        data_per_message = []
        for msg_id in sorted_messages:
            msg_data = {
                'occurrences': [],
                'id': msg_id,
                'title': sorted_messages[msg_id][0].symbol,
                'num_occurrences': len(sorted_messages[msg_id])
            }
            for msg_instance in sorted_messages[msg_id]:
                if msg_instance.node:
                    msg_data['has_node'] = True
                    msg_data['occurrences'].append({
                        'lineno': msg_instance.node.fromlineno,
                        'end_lineno': msg_instance.node.end_lineno,
                        'col_offset': msg_instance.node.col_offset,
                        'end_col_offset': msg_instance.node.end_col_offset,
                        'text': msg_instance.msg.split('\n')[0]
                    })
                else:
                    # TODO: use more accurate location data.
                    # [See some message-specific policies set `start` and `stop`
                    # locations in `node_printers.py` -- Instead, for now use
                    # location of the line.]
                    msg_data['has_node'] = False
                    if len(self._source_lines) == 0:
                        continue
                    msg_data['occurrences'].append({
                        'lineno': msg_instance.line,
                        'end_lineno': msg_instance.line,
                        'col_offset': msg_instance.column,
                        'end_col_offset': len(self._source_lines[msg_instance.line-1]),
                        'text': msg_instance.msg.split('\n')[0]
                    })
            data_per_message.append(msg_data)
        return data_per_message

    def print_messages(self, level='all'):
        """Collect data from all messages, using one result per file."""
        self.sort_messages()
        result = {
            'filename': self.current_file_linted,
            'num_errors': len(self._sorted_error_messages),
            'num_styles': len(self._sorted_style_messages),
            'msg_styles': self.build_result(self._sorted_style_messages),
            'msg_errors': self.build_result(self._sorted_error_messages)
        }
        # Update total counts
        self._output['total_genre_errors'] += result['num_errors']
        self._output['total_genre_styles'] += result['num_styles']
        self._output['total_results'] += 1
        self._output['results'].append(result)

    def output_blob(self):
        """Output python dict to JSON."""
        print(json.dumps(self._output, indent=4))
