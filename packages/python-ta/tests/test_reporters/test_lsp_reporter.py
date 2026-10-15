import json
import os
from io import StringIO
from pathlib import Path

import pytest

from python_ta import check_all

FIXTURE_PATH = os.path.normpath(
    os.path.join(__file__, "../../fixtures/reporters/lsp_reporter_input.py")
)
MISSING_DOCSTRING_FIXTURE_PATH = str(
    Path(FIXTURE_PATH).with_name("lsp_reporter_missing_docstring.py")
)


@pytest.fixture()
def lsp_output():
    """Run check_all with LSPReporter and return parsed JSON output."""
    buf = StringIO()
    check_all(
        module_name=[FIXTURE_PATH, MISSING_DOCSTRING_FIXTURE_PATH],
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
                        "start": {"line": 5, "character": 4},
                        "end": {"line": 5, "character": 5},
                    },
                    "message": "The variable x is unused and can be removed. If you intended to use it, there may be a typo elsewhere in the code.",
                    "severity": 2,
                    "code": "W0612",
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
