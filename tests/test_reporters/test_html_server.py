import os
import pprint
import re
import signal
import subprocess
import sys
import threading
import time
from http.client import HTTPConnection, RemoteDisconnected
from unittest.mock import patch

import pytest
import requests

from python_ta.reporters.html_server import open_html_in_browser


def wait_for_server(port: int, timeout: int = 30, interval: int = 1):
    """
    Wait for the server to be available before sending requests.

    """
    start_time = time.time()
    while time.time() - start_time < timeout:
        try:
            conn = HTTPConnection("127.0.0.1", port, timeout=1)
            conn.request("HEAD", "/")
            conn.getresponse()
            return True
        except (ConnectionRefusedError, OSError):
            time.sleep(interval)
    return False


@patch("webbrowser.open")
def test_open_html_in_browser_no_watch(mock_webbrowser_open):
    """
    Test the open_html_in_browser function with watch=False.
    Ensure the server handles a single request and shuts down properly.
    """
    html_content = b"<html><body><h1>Test HTML - No Watch</h1></body></html>"
    mock_webbrowser_open.return_value = True
    thread = threading.Thread(target=open_html_in_browser, args=(html_content, False, 0))
    thread.start()
    thread.join(timeout=0.1)

    args, _ = mock_webbrowser_open.call_args
    port = int(args[0].split(":")[2])

    conn = HTTPConnection("127.0.0.1", port)
    conn.request("GET", "/")
    response = conn.getresponse()

    assert response.status == 200
    assert response.read() == html_content

    with pytest.raises((ConnectionRefusedError, RemoteDisconnected)):
        new_conn = HTTPConnection("127.0.0.1", port)
        new_conn.request("GET", "/")
        new_conn.getresponse()
    conn.close()
    new_conn.close()


def test_open_html_in_browser_watch():
    """
    Test the open_html_in_browser function with watch=True using a fixed port.
    Ensure the server handles multiple requests and can be stopped gracefully.
    """
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/watch_integration.py")
    )
    process = subprocess.Popen([sys.executable, script_path])

    if not wait_for_server(5008):
        process.send_signal(signal.SIGINT)
        assert False

    try:
        for _ in range(3):
            conn = HTTPConnection("127.0.0.1", 5008)
            conn.request("GET", "/")
            response = conn.getresponse()
            assert response.status == 200
    finally:
        process.send_signal(signal.SIGINT)
