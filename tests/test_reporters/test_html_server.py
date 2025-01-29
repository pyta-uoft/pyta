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
    script_path = os.path.expanduser("~/pyta/tests/test_reporters/watch_integration.py")
    print(f"SCRIPT PATH IS OG is {script_path}")
    script_path = os.path.abspath(
        os.path.join(os.getcwd(), "tests", "test_reporters", "watch_integration.py")
    )
    print(f"SCRIPT PATH IS {script_path}")
    process = subprocess.Popen(
        [sys.executable, script_path],
        cwd=os.getcwd(),
    )

    time.sleep(60)
    try:
        for _ in range(3):
            conn = HTTPConnection("127.0.0.1", 5008)
            conn.request("GET", "/")
            response = conn.getresponse()
            assert response.status == 200
    finally:
        process.send_signal(signal.SIGINT)
