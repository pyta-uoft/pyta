import json

import attrs
from lsprotocol import types
from pylint.lint import PyLinter
from pylint.reporters.ureports.nodes import BaseLayout

from .core import NewMessage, PythonTaReporter

category_to_lsp = {
    "error": types.DiagnosticSeverity.Error,
    "fatal": types.DiagnosticSeverity.Error,
    "warning": types.DiagnosticSeverity.Warning,
    "convention": types.DiagnosticSeverity.Information,
    "refactor": types.DiagnosticSeverity.Hint,
}


def _lsp_severity(category: str) -> types.DiagnosticSeverity:
    """Convert the PyLint category to DiagnosticSeverity type, return default of warning"""
    return category_to_lsp.get(category, types.DiagnosticSeverity.Warning)


def _serialize(inst, field, value):
    if isinstance(value, types.DiagnosticSeverity):
        return value.value
    return value


class LSPReporter(PythonTaReporter):

    name = "pyta-lsp"
    OUTPUT_FILENAME = "pyta_lsp_report.json"
    messages: dict[str, list[NewMessage]]

    def display_messages(self, layout: BaseLayout) -> None:
        json_output = {}
        for filename, msgs in self.gather_messages().items():
            diagnostics_list = []
            for msg in msgs:
                diag = types.Diagnostic(
                    range=types.Range(
                        start=types.Position(line=msg.line - 1, character=msg.column or 0),
                        end=types.Position(
                            line=(msg.end_line or msg.line) - 1, character=msg.end_column or 0
                        ),
                    ),
                    message=msg.msg,
                    severity=_lsp_severity(msg.category),
                    code=msg.msg_id,
                    source="python-ta",
                )
                diagnostics_list.append(attrs.asdict(diag, value_serializer=_serialize))
            json_output[filename] = diagnostics_list
        self.writeln(json.dumps(json_output, indent=4))
        self.out.flush()


def register(linter: PyLinter):
    linter.register_reporter(LSPReporter)
