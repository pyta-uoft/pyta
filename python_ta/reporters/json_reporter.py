import json
from typing import Dict, List

from pylint.reporters.ureports.nodes import BaseLayout

from .core import NewMessage, PythonTaReporter


class JSONReporter(PythonTaReporter):
    """Reporter that outputs JSON.

    Based on Pylint's JSONReporter.
    """

    name = "JSONReporter"

    OUTPUT_FILENAME = "pyta_report.json"

    messages: Dict[str, List[NewMessage]]

    def display_messages(self, layout: BaseLayout) -> None:
        """Hook for displaying the messages of the reporter

        This will be called whenever the underlying messages
        needs to be displayed. For some reporters, it probably
        doesn't make sense to display messages as soon as they
        are available, so some mechanism of storing them could be used.
        This method can be implemented to display them after they've
        been aggregated.
        """
        output = []
        for k, msgs in self.messages.items():
            output.append(
                {
                    "filename": k,
                    "msgs": self._output_messages(msgs),
                }
            )

        self.writeln(json.dumps(output, indent=4))

    def _output_messages(self, msgs: list[NewMessage]) -> list:
        """Return list of dictionaries of properly formatted members of the messages list."""
        max_messages = self.linter.config.pyta_number_of_messages
        output_lst = []
        all_msg_names = [msg.message.msg_id for msg in msgs]

        unique_msg_names = []
        [
            unique_msg_names.append(msg_id)
            for msg_id in all_msg_names
            if msg_id not in unique_msg_names
        ]

        for msg_id in unique_msg_names:
            num_messages = 0
            for msg in msgs:
                if max_messages == 0 or (
                    msg.message.msg_id == msg_id and num_messages < max_messages
                ):
                    message_dict = msg.to_dict()
                    message_dict["number_of_occurrences"] = all_msg_names.count(msg.message.msg_id)

                    if message_dict not in output_lst:
                        output_lst.append(message_dict)
                    num_messages += 1

        return output_lst
