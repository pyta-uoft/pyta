import json
from pathlib import Path

from lsprotocol import converters, types
from pylint.lint import PyLinter
from pylint.message import Message
from pylint.reporters.ureports.nodes import Section

from .core import MessageLike, PythonTaReporter
from python_ta.util.documentation import get_documentation_url
from python_ta.util.source_positions import (
    codepoint_offset_to_utf16,
    message_column_to_utf16,
)

CATEGORY_TO_LSP = {
    "error": types.DiagnosticSeverity.Error,
    "fatal": types.DiagnosticSeverity.Error,
    "warning": types.DiagnosticSeverity.Warning,
    "convention": types.DiagnosticSeverity.Information,
    "refactor": types.DiagnosticSeverity.Hint,
}

# Deprecation-related checks, including disabled checks.
DEPRECATION_CHECKS = {
    "deprecated-module",
    "deprecated-method",
    "deprecated-argument",
    "deprecated-class",
    "deprecated-decorator",
    "deprecated-attribute",
    "deprecated-pragma",
    "deprecated-typing-alias",
}


def _lsp_severity(category: str) -> types.DiagnosticSeverity:
    """Convert the Pylint category to DiagnosticSeverity type, return default of warning"""
    return CATEGORY_TO_LSP.get(category, types.DiagnosticSeverity.Warning)


class LSPReporter(PythonTaReporter):
    """Reporter that displays results in Language Server Protocol (LSP) compliant JSON format"""

    name = "pyta-lsp"
    OUTPUT_FILENAME = "pyta_lsp_report.json"
    messages: dict[str, list[MessageLike]]

    def handle_message(self, msg: Message) -> None:
        """Update the message's location while its source lines are available."""
        self._update_message_range(msg)
        super().handle_message(msg)

    def _update_message_range(self, msg: Message) -> None:
        """Mutate the message's range to use LSP's default UTF-16 position encoding."""
        if 1 <= msg.line <= len(self.source_lines):
            msg.column = message_column_to_utf16(
                self.source_lines[msg.line - 1], msg.column or 0, msg.symbol
            )

        end_line = msg.end_line or msg.line
        if msg.end_column is not None and 1 <= end_line <= len(self.source_lines):
            msg.end_column = message_column_to_utf16(
                self.source_lines[end_line - 1],
                msg.end_column,
                msg.symbol,
                is_end=True,
            )

        # Highlight only the first line of full-module messages
        if (
            self.source_lines
            and msg.line == 1
            and msg.column == 0
            and end_line == len(self.source_lines)
            and msg.end_column
            == codepoint_offset_to_utf16(self.source_lines[-1], len(self.source_lines[-1]))
        ):
            msg.end_line = msg.line
            msg.end_column = codepoint_offset_to_utf16(
                self.source_lines[0], len(self.source_lines[0])
            )

    def display_messages(self, layout: Section | None) -> None:
        output: list[dict] = []
        converter = converters.get_converter()

        for filename, msgs in self.gather_messages().items():
            diagnostics_list: list[types.Diagnostic] = []
            for msg in msgs:
                start_char = msg.column or 0
                if msg.end_column is not None:
                    end_char = msg.end_column
                else:
                    end_char = start_char
                diag = types.Diagnostic(
                    range=types.Range(
                        start=types.Position(line=msg.line - 1, character=start_char),
                        end=types.Position(line=(msg.end_line or msg.line) - 1, character=end_char),
                    ),
                    message=msg.msg,
                    severity=_lsp_severity(msg.category),
                    code=msg.msg_id,
                    code_description=types.CodeDescription(href=get_documentation_url(msg.msg_id)),
                    source="python-ta",
                    tags=(
                        [types.DiagnosticTag.Deprecated]
                        if msg.symbol in DEPRECATION_CHECKS
                        else None
                    ),
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
