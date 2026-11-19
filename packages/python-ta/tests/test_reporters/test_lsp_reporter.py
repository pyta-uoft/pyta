import json
import os
from io import StringIO
from pathlib import Path

import pytest
from lsprotocol.types import DiagnosticSeverity, DiagnosticTag

from python_ta import check_all, doc
from python_ta.reporters.lsp_reporter import LSPReporter

FIXTURE_PATH = os.path.normpath(
    os.path.join(__file__, "../../fixtures/reporters/lsp_reporter_input.py")
)
MISSING_DOCSTRING_FIXTURE_PATH = str(
    Path(FIXTURE_PATH).with_name("lsp_reporter_missing_docstring.py")
)
DEPRECATED_ATTRIBUTE_FIXTURE_PATH = str(
    Path(FIXTURE_PATH).with_name("lsp_reporter_deprecated_attribute.py")
)


@pytest.fixture()
def lsp_output():
    """Run check_all with LSPReporter and return parsed JSON output."""
    buf = StringIO()
    check_all(
        module_name=[
            FIXTURE_PATH,
            MISSING_DOCSTRING_FIXTURE_PATH,
            DEPRECATED_ATTRIBUTE_FIXTURE_PATH,
        ],
        config={"output-format": "pyta-lsp"},
        output=buf,
    )
    buf.seek(0)
    return json.loads(buf.read())


def test_exact_output(lsp_output):

    expected = [
        {
            "uri": Path(FIXTURE_PATH).resolve().as_uri(),
            "diagnostics": [
                {
                    "range": {
                        "start": {"line": 5, "character": 17},
                        "end": {"line": 5, "character": 26},
                    },
                    "message": "Undefined variable 'undefined'",
                    "severity": 1,
                    "code": "E0602",
                    "codeDescription": {
                        "href": "https://www.cs.toronto.edu/~david/pyta/checkers/index.html#e0602"
                    },
                    "source": "python-ta",
                }
            ],
        }
    ]

    assert lsp_output[0] == expected[0]


def test_module_diagnostic_highlights_only_first_line(lsp_output):
    """Tests that only the first line is highlighted when the message is for the entire module,
    such as for a missing module docstring."""

    diagnostics = lsp_output[1]["diagnostics"]
    module_diagnostic = next(
        diagnostic for diagnostic in diagnostics if diagnostic["code"] == "C0114"
    )

    assert module_diagnostic["range"] == {
        "start": {"line": 0, "character": 0},
        "end": {"line": 0, "character": 13},
    }


def test_code_description_matches_doc(lsp_output, mocker):
    """Tests that each diagnostic links to the same URL opened by python_ta.doc."""
    open_browser = mocker.patch("webbrowser.open")

    for output in lsp_output:
        for diagnostic in output["diagnostics"]:
            doc(diagnostic["code"])
            open_browser.assert_called_with(diagnostic["codeDescription"]["href"])


def test_deprecated_attribute_tag(lsp_output):
    """Tests that deprecation checks are emitted with the Deprecated tag."""
    diagnostics = lsp_output[2]["diagnostics"]
    diagnostic = next(diag for diag in diagnostics if diag["code"] == "W4906")
    assert diagnostic["tags"] == [DiagnosticTag.Deprecated]
    assert diagnostic["severity"] == DiagnosticSeverity.Warning


def test_unicode_module_diagnostic_highlights_only_first_line(mocker):
    """Test full-module range detection when the first and last lines contain Unicode."""
    reporter = LSPReporter()
    reporter.source_lines = ["😀", "é"]
    message = mocker.Mock(
        symbol="missing-module-docstring",
        line=1,
        column=0,
        end_line=2,
        end_column=2,
    )

    reporter._update_message_range(message)

    assert message.line == 1
    assert message.column == 0
    assert message.end_line == 1
    assert message.end_column == 2
