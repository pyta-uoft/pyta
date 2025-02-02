import os
import signal
import subprocess
import sys
import threading
import time
from http.client import HTTPConnection, RemoteDisconnected
from unittest.mock import patch

import pytest

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


def test_open_html_in_browser_no_watch():
    """
    Test the open_html_in_browser function with watch=False.
    Ensure the server handles a single request and shuts down properly.
    """

    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/no_watch_integration.py")
    )
    process = subprocess.Popen([sys.executable, script_path])
    if not wait_for_server(5008):
        process.send_signal(signal.SIGINT)
        pytest.fail("Server did not start within the expected timeout")
    try:
        with pytest.raises((ConnectionRefusedError, RemoteDisconnected)):
            new_conn = HTTPConnection("127.0.0.1", 5008)
            new_conn.request("GET", "/")
            new_conn.getresponse()
    finally:
        process.send_signal(signal.SIGINT)


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
        pytest.fail("Server did not start within the expected timeout")

    try:
        for i in range(3):
            conn = HTTPConnection("127.0.0.1", 5008)
            conn.request("GET", "/")
            response = conn.getresponse()
            assert response.status == 200

    finally:
        process.send_signal(signal.SIGINT)
