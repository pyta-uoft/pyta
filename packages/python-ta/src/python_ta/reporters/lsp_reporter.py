import json
from pathlib import Path

from lsprotocol import converters, types
from pylint.lint import PyLinter
from pylint.reporters.ureports.nodes import BaseLayout

from .core import NewMessage, PythonTaReporter

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
    messages: dict[str, list[NewMessage]]

    def display_messages(self, layout: BaseLayout) -> None:
        output = []
        converter = converters.get_converter()

        for filename, msgs in self.gather_messages().items():
            diagnostics_list = []
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


def register(linter: PyLinter):
    linter.register_reporter(LSPReporter)
