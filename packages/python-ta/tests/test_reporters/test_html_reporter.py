import os
import signal
import subprocess
import sys
from http.client import HTTPConnection

import pytest
from tests.test_reporters.test_html_server import clean_response_body, wait_for_server

escaped_script = "&quot;&lt;script&gt;alert(2);&lt;/script&gt;&quot;"


def test_injection(snapshot):
    """Test the HTML injection is properly escaped and is not executed as HTML code"""
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/content_injection.py")
    )

    process = subprocess.Popen([sys.executable, script_path])

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
        cleaned_body = clean_response_body(response_body)
        assert escaped_script in cleaned_body
        snapshot.assert_match(cleaned_body, "script_injection.html")
    finally:
        process.send_signal(signal.SIGTERM)
        process.wait()
