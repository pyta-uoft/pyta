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
                    "msgs": [msg.to_dict() for msg in msgs],
                }
            )

        self.writeln(json.dumps(output, indent=4))
