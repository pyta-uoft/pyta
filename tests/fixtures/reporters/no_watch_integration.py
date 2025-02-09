"""This script serves as the entry point for an integration test of the PyTA HTML report server.
It is invoked by the test `tests/test_reporters/test_html_server::test_open_html_in_browser_no_watch()`
to verify that the HTML report server can handle multiple requests when `watch=True`."""

from unittest.mock import patch

from python_ta import check_all


@patch("webbrowser.open", return_value=None)
def open_server(mock_webbrowser_open):
    check_all(
        config={
            "watch": False,
            "server_port": 5008,
        }
    )


open_server()
