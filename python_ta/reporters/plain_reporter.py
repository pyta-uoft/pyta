from typing import Dict, List

from pylint.interfaces import IReporter
from .core import NewMessage, PythonTaReporter


class PlainReporter(PythonTaReporter):
    """Plain text reporter."""
    __implements__ = IReporter
    name = 'PlainReporter'

    OUTPUT_FILENAME = 'pyta_report.txt'

    # Rendering constants
    _SPACE = ' '
    _BREAK = '\n'
    _COLOURING = {}
    code_err_title = '=== Code errors/forbidden usage (fix: high priority) ==='
    style_err_title = '=== Style/convention errors (fix: before submission) ==='
    no_err_message = 'None!' + _BREAK * 2
    no_snippet = 'Nothing here.' + _BREAK * 2

    def print_messages(self, level: str = 'all') -> None:
        """Print messages for the current file.

        If level == 'all', both errors and style errors are displayed. Otherwise,
        only errors are displayed.
        """
        error_msgs, style_msgs = self.group_messages(self.messages[self.current_file])

        result = 'PyTA Report for: ' + self._colourify('bold', self.current_file) + self._BREAK
        result += self._colourify('code-heading', self.code_err_title + self._BREAK)
        messages_result = self._colour_messages_by_type(error_msgs)
        if messages_result:
            result += messages_result
        else:
            result += self.no_err_message

        if level == 'all':
            result += self._colourify('style-heading', self.style_err_title + self._BREAK)
            messages_result = self._colour_messages_by_type(style_msgs)
            if messages_result:
                result += messages_result
            else:
                result += self.no_err_message

        self.writeln(result)

    def _colour_messages_by_type(self, messages: Dict[str, List[NewMessage]]) -> str:
        """
        Return string of properly formatted members of the messages dict
        (error or style) indicated by style.
        """
        max_messages = self.linter.config.pyta_number_of_messages

        result = ''
        for msg_id in messages:
            result += self._colourify('bold', msg_id)
            result += self._colourify('bold', ' ({})  '.format(messages[msg_id][0].symbol))
            result += 'Number of occurrences: {}.'.format(len(messages[msg_id]))
            if max_messages != float('inf') and max_messages < len(messages[msg_id]):
                result += ' (First {} shown).'.format(max_messages)
            result += self._BREAK

            for i, msg in enumerate(messages[msg_id]):
                if i == max_messages:
                    break

                # Use only explanation, without redundant accessory information
                msg_truncated = msg.msg.split('\n')[0]
                result += 2 * self._SPACE
                result += self._colourify('bold', '[Line {}] {}'
                            .format(msg.line, msg_truncated)) + self._BREAK

                result += msg.snippet
                result += self._BREAK

        return result
