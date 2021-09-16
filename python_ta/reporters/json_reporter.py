import json
from typing import Dict, List

from pylint.interfaces import IReporter
from pylint.reporters.ureports.nodes import BaseLayout

from .core import NewMessage, PythonTaReporter


class JSONReporter(PythonTaReporter):
    """Reporter that outputs JSON.

    Based on Pylint's JSONReporter.
    """

    __implements__ = IReporter
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
                    "msgs": [
                        {**msg._replace(node=None)._asdict(), **self._snippet_endings(msg)}
                        for msg in msgs
                    ],
                }
            )

        self.writeln(json.dumps(output, indent=4))

    def _snippet_endings(self, msg: NewMessage) -> Dict[str, int]:
        """Return a dictionary containing the index of the last line and the index of the last column of the
        error reported by the message in msg.
        """
        if msg.node is None:
            line_end, column_end = msg.line, len(self.source_lines[msg.line - 1])
        else:
            line_end, column_end = msg.node.end_lineno, msg.node.end_col_offset
        return {"line_end": line_end, "column_end": column_end}
