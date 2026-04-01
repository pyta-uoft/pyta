import json
import os
from io import StringIO
from pathlib import Path

import pytest

from python_ta import check_all

FIXTURE_PATH = os.path.normpath(
    os.path.join(__file__, "../../fixtures/reporters/lsp_reporter_input.py")
)


@pytest.fixture()
def lsp_output():
    """Run check_all with LSPReporter and return parsed JSON output."""
    buf = StringIO()
    check_all(
        module_name=FIXTURE_PATH,
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

    assert lsp_output == expected
