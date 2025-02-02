import os
import re
import signal
import subprocess
import sys
import time
from http.client import HTTPConnection, RemoteDisconnected

import pytest


def save_snapshot(data, snapshot_file):
    """Save the response snapshot for comparison."""
    with open(snapshot_file, "w") as f:
        f.write(data)


def load_snapshot(snapshot_file):
    """Load the saved response snapshot."""
    if not os.path.exists(snapshot_file):
        return None
    with open(snapshot_file, "r") as f:
        return f.read()


def clean_response_body(body):
    """
    Remove dynamic portions (such as timestamps) from the response body
    before snapshot testing.
    """
    return re.sub(r"\d{2}:\d{2}:\d{2}", "[TIME]", body)


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

    snapshot_file = os.path.normpath(
        os.path.join(__file__, "../snapshot/no_watch_html_server_snapshot.txt")
    )

    process = subprocess.Popen([sys.executable, script_path])

    start_time = time.time()
    timeout = 15
    response_body = None

    try:
        # Wait for the server to start
        while time.time() - start_time < timeout:
            try:
                conn = HTTPConnection("127.0.0.1", 5008, timeout=1)
                conn.request("GET", "/")
                response = conn.getresponse()
                assert response.status == 200
                response_body = response.read().decode("utf-8")
                break
            except (ConnectionRefusedError, OSError):
                time.sleep(0.5)

        if response_body is None:
            pytest.fail("Server did not start within the expected timeout")

        cleaned_body = clean_response_body(response_body)
        snapshot = load_snapshot(snapshot_file)
        assert cleaned_body == snapshot

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

    snapshot_file = os.path.normpath(
        os.path.join(__file__, "../snapshot/watch_html_server_snapshot.txt")
    )

    process = subprocess.Popen([sys.executable, script_path])

    if not wait_for_server(5008):
        process.send_signal(signal.SIGINT)
        pytest.fail("Server did not start within the expected timeout")

    try:
        snapshot = load_snapshot(snapshot_file)

        print("ORIGINAL SNAPSHOT FILE:: \n\n\n\n")
        print(snapshot)

        for i in range(3):
            conn = HTTPConnection("127.0.0.1", 5008)
            conn.request("GET", "/")
            response = conn.getresponse()
            assert response.status == 200

            response_body = response.read().decode("utf-8")
            cleaned_body = clean_response_body(response_body)

            print("CLEANED BODY:: \n\n\n\n")
            print(cleaned_body)

            assert cleaned_body == snapshot

    finally:
        process.send_signal(signal.SIGINT)
