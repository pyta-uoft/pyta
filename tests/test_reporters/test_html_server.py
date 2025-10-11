import os
import re
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
    body = re.sub(
        r".*tests[/\\]fixtures[/\\]reporters[/\\](?:no_)?watch_integration\.py.*\n?", "", body
    )
    body = re.sub(r'\s*<span class="pygments-w">\s*</span>\s*<span', " <span", body)
    body = re.sub(r"^.*[/\\]watch_integration.py.*$", "", body, flags=re.MULTILINE)

    return body.strip()


def updated_html_from_server(
    initial_html: str, timeout: int = 30, interval: int = 1
) -> Optional[str]:
    """Waits for the server to update its html contents before returning the new html string. Polls the server
    every interval seconds until timeout seconds have passed at which point the function returns None.
    """
    start_time = time.time()
    while time.time() - start_time < timeout:
        conn = HTTPConnection("127.0.0.1", 5008, timeout=1)
        conn.request("GET", "/")
        response = conn.getresponse()
        clean_response = clean_response_body(response.read().decode("utf-8"))
        if clean_response != initial_html:
            return clean_response
        time.sleep(interval)
    return None


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
            process.send_signal(signal.SIGTERM)
            process.wait()
            pytest.fail("Server did not start within the expected timeout")

        cleaned_body = clean_response_body(response_body)
        snapshot.assert_match(cleaned_body, "no_watch_html_server_snapshot.html")

        with pytest.raises((ConnectionRefusedError, RemoteDisconnected)):
            new_conn = HTTPConnection("127.0.0.1", 5008)
            new_conn.request("GET", "/")
            new_conn.getresponse()
    finally:
        process.send_signal(signal.SIGTERM)
        process.wait()


def test_watch_persistence(snapshot):
    """Test the open_html_in_browser function with watch=True using a fixed port.
    Ensure the server handles multiple requests and can be stopped gracefully."""
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/watch_integration.py")
    )

    process = subprocess.Popen([sys.executable, script_path])

    if not wait_for_server(5008):
        process.send_signal(signal.SIGTERM)
        process.wait()
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
        process.send_signal(signal.SIGTERM)
        process.wait()


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
        process.send_signal(signal.SIGTERM)
        process.wait()
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

        cleaned_body_after = updated_html_from_server(cleaned_body_before)
        if cleaned_body_after is None:
            pytest.fail("Server did not update HTML code served")
        else:
            snapshot.assert_match(cleaned_body_after, "watch_html_server_snapshot_updated.html")

    finally:
        process.send_signal(signal.SIGTERM)
        process.wait()


def test_websocket_message(temp_script_file_path):
    """Test that the "reload" message is sent to any open websocket connections
    upon update to the files being watched
    """
    process = subprocess.Popen([sys.executable, temp_script_file_path])

    try:
        if not wait_for_server(5008):
            pytest.fail("Server did not start within the expected timeout")

        ws = websocket.create_connection("ws://localhost:5008/ws", timeout=10)

        with open(temp_script_file_path, "a") as py_file:
            py_file.write("# trigger reload\n")

        message = ws.recv()
        assert message == "reload"
    finally:
        try:
            ws.close()
        except Exception:
            pass
        process.send_signal(signal.SIGTERM)
        process.wait()
