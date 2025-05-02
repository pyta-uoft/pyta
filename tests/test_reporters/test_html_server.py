import os
import re
import select
import signal
import subprocess
import sys
import time
from http.client import HTTPConnection, RemoteDisconnected
from typing import Optional

import pytest
import websocket


def clean_response_body(body) -> str:
    """Remove dynamic portions (such as timestamps) from the response body
    before snapshot testing."""
    body = re.sub(r".*<time>.*?</time>.*\n?", "", body)
    body = re.sub(r".*tests/fixtures/reporters/(?:no_)?watch_integration\.py.*\n?", "", body)
    body = re.sub(r'\s*<span class="pygments-w">\s*</span>\s*<span', " <span", body)
    body = re.sub(r"^.*/watch_integration.py.*$", "", body, flags=re.MULTILINE)

    return body.strip()

def server_does_update_on_change(initial_html: str, timeout: int = 30, interval: int = 1) -> bool:
    start_time = time.time()
    while time.time() - start_time < timeout:
        conn = HTTPConnection("127.0.0.1",5008 , timeout=1)
        conn.request("GET", "/")
        response = conn.getresponse()
        clean_response = clean_response_body(response.read().decode("utf-8"))
        if clean_response != initial_html:
            return True
        time.sleep(interval)
    return False

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


def test_no_watch_server_is_non_persistent(snapshot):
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


def test_watch_persistence(snapshot):
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


@pytest.fixture(scope="function")
def temp_script_file_path(tmp_path) -> str:
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/watch_integration.py")
    )
    with open(script_path, "r") as file:
        lines = file.readlines()

    file_path = os.path.join(tmp_path, "watch_integration.py")
    with open(file_path, "w") as temp_file:
        temp_file.writelines(lines)

    return file_path



def test_watch_update(temp_script_file_path, snapshot):
    """Test the start_server_once function with watch=True using a fixed port.
    Ensure the server changes the report contents after making code changes"""

    process = subprocess.Popen([sys.executable, temp_script_file_path])

    if not wait_for_server(5008):
        process.send_signal(signal.SIGINT)
        pytest.fail("Server did not start within the expected timeout")

    try:
        conn = HTTPConnection("127.0.0.1", 5008)
        conn.request("GET", "/")
        response = conn.getresponse()
        assert response.status == 200

        response_body = response.read().decode("utf-8")
        cleaned_body_before = clean_response_body(response_body)
        snapshot.assert_match(cleaned_body_before, "watch_html_server_snapshot.html")

        with open(temp_script_file_path, "a") as py_file:
            py_file.write("# This doesn't belong here!")

        if not server_does_update_on_change(cleaned_body_before):
            pytest.fail("Server did not update HTML code served")

    finally:
        process.send_signal(signal.SIGINT)


def test_websocket_message(temp_script_file_path):
    """Test that the "reload" message is sent to any open websocket connections
    upon update to the files being watched
    """
    process = subprocess.Popen([sys.executable, temp_script_file_path])

    try:
        if not wait_for_server(5008):
            pytest.fail("Server did not start within the expected timeout")

        ws = websocket.create_connection("ws://localhost:5008/ws")
        ws.settimeout(1)

        with open(temp_script_file_path, "a") as py_file:
            py_file.write("# trigger reload\n")

        time.sleep(2)  # give the server time to send the websocket message

        message = ws.recv()
        assert message == "reload"
    finally:
        try:
            ws.close()
        except Exception:
            pass
        process.send_signal(signal.SIGINT)
