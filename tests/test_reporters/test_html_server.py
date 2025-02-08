import os
import re
import signal
import subprocess
import sys
import time
from http.client import HTTPConnection, RemoteDisconnected
from typing import Optional

import pytest


def clean_response_body(body) -> str:
    """Remove dynamic portions (such as timestamps) from the response body
    before snapshot testing."""
    body = re.sub(r".*<time>.*?</time>.*\n?", "", body)
    body = re.sub(r".*tests/fixtures/reporters/(?:no_)?watch_integration\.py.*\n?", "", body)
    body = re.sub(r'\s*<span class="pygments-w">\s*</span>\s*<span', " <span", body)  # Fixed regex

    return body.strip()


def wait_for_server(port: int, timeout: int = 30, interval: int = 1) -> Optional[str]:
    """Wait for the server to be available before sending requests."""
    start_time = time.time()
    while time.time() - start_time < timeout:
        try:
            conn = HTTPConnection("127.0.0.1", port, timeout=1)
            conn.request("GET", "/")
            response = conn.getresponse()
            return response.read().decode("utf-8")
        except (ConnectionRefusedError, OSError):
            time.sleep(interval)
    return None


def test_open_html_in_browser_no_watch(snapshot):
    """Test the open_html_in_browser function with watch=False.
    Ensure the server handles a single request and shuts down properly."""

    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/no_watch_integration.py")
    )

    process = subprocess.Popen([sys.executable, script_path])

    try:
        response_body = wait_for_server(5008)

        if not response_body:
            process.send_signal(signal.SIGINT)
            pytest.fail("Server did not start within the expected timeout")

        cleaned_body = clean_response_body(response_body)

        snapshot.assert_match(cleaned_body, "no_watch_html_server_snapshot.html")

        with pytest.raises((ConnectionRefusedError, RemoteDisconnected)):
            new_conn = HTTPConnection("127.0.0.1", 5008)
            new_conn.request("GET", "/")
            new_conn.getresponse()
    finally:
        process.send_signal(signal.SIGINT)


def test_open_html_in_browser_watch(snapshot):
    """Test the open_html_in_browser function with watch=True using a fixed port.
    Ensure the server handles multiple requests and can be stopped gracefully."""
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

            response_body = response.read().decode("utf-8")
            cleaned_body = clean_response_body(response_body)
            snapshot.assert_match(cleaned_body, "watch_html_server_snapshot.html")

    finally:
        process.send_signal(signal.SIGINT)
