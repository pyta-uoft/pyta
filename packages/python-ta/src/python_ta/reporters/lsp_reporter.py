import json
from pathlib import Path

from lsprotocol import converters, types
from pylint.lint import PyLinter
from pylint.message import Message
from pylint.reporters.ureports.nodes import Section

from .core import MessageLike, PythonTaReporter

CATEGORY_TO_LSP = {
    "error": types.DiagnosticSeverity.Error,
    "fatal": types.DiagnosticSeverity.Error,
    "warning": types.DiagnosticSeverity.Warning,
    "convention": types.DiagnosticSeverity.Information,
    "refactor": types.DiagnosticSeverity.Hint,
}


def _lsp_severity(category: str) -> types.DiagnosticSeverity:
    """Convert the Pylint category to DiagnosticSeverity type, return default of warning"""
    return CATEGORY_TO_LSP.get(category, types.DiagnosticSeverity.Warning)


class LSPReporter(PythonTaReporter):
    """Reporter that displays results in Language Server Protocol (LSP) compliant JSON format"""

    name = "pyta-lsp"
    OUTPUT_FILENAME = "pyta_lsp_report.json"
    messages: dict[str, list[MessageLike]]
    _message_ranges: dict[str, list[types.Range]]

    def __init__(self) -> None:
        super().__init__()
        self._message_ranges = {}

    def handle_message(self, msg: Message) -> None:
        """Handle the message and store the message ranges while source_lines belongs to this message's file."""
        if not self.messages[self.current_file]:
            self._message_ranges[self.current_file] = []
        super().handle_message(msg)
        self._message_ranges[self.current_file].append(self._get_message_range(msg))

    def _get_message_range(self, msg: MessageLike) -> types.Range:
        """
        Return the message diagnostic range.
        Highlight only the first line of full-module messages.
        """
        start_char = msg.column or 0
        end_line = msg.end_line or msg.line
        end_char = msg.end_column if msg.end_column is not None else start_char

        if self.source_lines and (
            msg.line == 1
            and start_char == 0
            and end_line == len(self.source_lines)
            and end_char == len(self.source_lines[-1])
        ):
            end_line = msg.line
            end_char = len(self.source_lines[0])
        return types.Range(
            start=types.Position(line=msg.line - 1, character=start_char),
            end=types.Position(line=end_line - 1, character=end_char),
        )

    def display_messages(self, layout: Section | None) -> None:
        output: list[dict] = []
        converter = converters.get_converter()

        for filename, msgs in self.gather_messages().items():
            diagnostics_list: list[types.Diagnostic] = []
            for msg, msg_range in zip(msgs, self._message_ranges.get(filename, [])):
                diag = types.Diagnostic(
                    range=msg_range,
                    message=msg.msg,
                    severity=_lsp_severity(msg.category),
                    code=msg.msg_id,
                    source="python-ta",
                )
                diagnostics_list.append(diag)

            params = types.PublishDiagnosticsParams(
                uri=Path(filename).resolve().as_uri(), diagnostics=diagnostics_list
            )
            output.append(
                converter.unstructure(params, unstructure_as=types.PublishDiagnosticsParams)
            )

        self.writeln(json.dumps(output, indent=4))
        self.out.flush()


def register(linter: PyLinter) -> None:
    linter.register_reporter(LSPReporter)
