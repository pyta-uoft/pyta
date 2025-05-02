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

def server_does_update_on_change(initial_html: str, timeout: int = 30, interval: int = 1) -> Optional[str]:
    start_time = time.time()
    while time.time() - start_time < timeout:
        conn = HTTPConnection("127.0.0.1",5008 , timeout=1)
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
        print("Cleaned HTML Body Before:")
        print(cleaned_body_before)
        print("End Cleaned HTML Body Before")
        snapshot.assert_match(cleaned_body_before, "watch_html_server_snapshot.html")



        with open(temp_script_file_path, "a") as py_file:
            py_file.write("# This doesn't belong here!")

        cleaned_body_after = server_does_update_on_change(cleaned_body_before)
        if cleaned_body_after is None:
            pytest.fail("Server did not update HTML code served")
        else:
            snapshot.assert_match(cleaned_body_after, "watch_html_server_snapshot_updated.html")

    finally:
        process.send_signal(signal.SIGINT)


