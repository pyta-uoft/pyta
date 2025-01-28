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
    thread = threading.Thread(target=open_html_in_browser, args=(html_content, False))
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
    process = subprocess.Popen(
        [sys.executable, "watch_integration.py"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    for _ in range(13):
        line = process.stderr.readline().strip()
        if "Server running at" in line:
            port_match = re.search(r"http://127\.0\.0\.1:(\d+)", line)
            if port_match:
                port = int(port_match.group(1))
                print(f"Extracted port: {port}")
                break

    try:
        for _ in range(3):
            conn = HTTPConnection("127.0.0.1", port)
            conn.request("GET", "/")
            response = conn.getresponse()
            assert response.status == 200
    finally:
        process.send_signal(signal.SIGINT)
