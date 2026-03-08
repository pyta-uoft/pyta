import json
import os
from io import StringIO

import pytest

from python_ta import check_all

FIXTURE_PATH = os.path.normpath(
    os.path.join(__file__, "../../fixtures/reporters/lsp_reporter_input.py")
)


@pytest.fixture()
def lsp_output(prevent_webbrowser_and_httpserver):
    """Run check_all with LSPReporter and return parsed JSON output."""
    buf = StringIO()
    check_all(
        module_name=FIXTURE_PATH,
        config={"output-format": "pyta-lsp"},
        output=buf,
    )
    buf.seek(0)
    return json.loads(buf.read())


def test_output_is_list(lsp_output):
    assert isinstance(lsp_output, list)


def test_uri_format(lsp_output):
    for entry in lsp_output:
        assert entry["uri"].startswith("file://")


def test_has_diagnostics_key(lsp_output):
    for entry in lsp_output:
        assert "diagnostics" in entry
        assert isinstance(entry["diagnostics"], list)


def test_line_numbers_valid_indexes(lsp_output):
    for entry in lsp_output:
        for diag in entry["diagnostics"]:
            assert diag["range"]["start"]["line"] >= 0
            assert diag["range"]["end"]["line"] >= 0


def test_severity_is_int(lsp_output):
    for entry in lsp_output:
        for diag in entry["diagnostics"]:
            assert isinstance(diag["severity"], int)
            assert diag["severity"] in (1, 2, 3, 4)
