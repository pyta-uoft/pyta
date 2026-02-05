"""This script serves as the entry point for the PyTA HTML reporter tests.
It is invoked by the test `tests/test_reporters/test_html_report::test_injection()`
to ensure that no HTML can be injected into the HTML report."""
from unittest.mock import patch

from python_ta import check_all

@patch("webbrowser.open", return_value=None)
def inject_script(mock_webbrowser_open):
    a = "hello"
    x = f'{a + "<script>alert(2);</script>"}'
    check_all(config={
        "watch": True,
        "server_port": 2000
    })

inject_script()