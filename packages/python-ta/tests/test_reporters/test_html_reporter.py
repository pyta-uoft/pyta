import os
import re

from tests.test_reporters.test_html_server import wait_for_server

from python_ta import check_all

ESCAPED_SCRIPT = "&quot;&lt;script&gt;alert(2);&lt;/script&gt;&quot;"
UNESCAPED_SCRIPT = "<script>alert(2);</script>"
ESCAPED_MARKDOWN = "&#96; ##world &#96;"
UNESCAPED_MARKDOWN = "</code> ##world <code>"


def clean_response_body(body) -> str:
    """Remove dynamic portions (such as timestamps) from the response body
    before snapshot testing."""
    body = re.sub(r".*<time>.*?</time>.*\n?", "", body)
    body = re.sub(r".*tests[/\\]fixtures[/\\]reporters[/\\]content_injection\.py.*\n?", "", body)
    body = re.sub(
        r".*tests[/\\]fixtures[/\\]reporters[/\\]markdown_escape_script\.py.*\n?", "", body
    )
    body = re.sub(r'\s*<span class="pygments-w">\s*</span>\s*<span', " <span", body)
    body = re.sub(r"localhost:\d+", "localhost:", body)

    return body.strip()


def test_injection(snapshot):
    """Test the HTML injection is properly escaped and is not executed as HTML code"""
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/content_injection.py")
    )
    output_path = os.path.normpath(
        os.path.join(__file__, "../../test_reporters/output_files/injection_script_output.html")
    )
    check_all(module_name=script_path, output=output_path)

    with open(output_path, "r") as output_file:

        response_body = output_file.read()
        cleaned_body = clean_response_body(response_body)

        assert ESCAPED_SCRIPT in cleaned_body
        assert UNESCAPED_SCRIPT not in cleaned_body

        snapshot.assert_match(cleaned_body, "script_injection.html")


def test_markdown_escape(snapshot):
    """Test markdown characters in error messages are properly escaped"""
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/markdown_escape_script.py")
    )
    output_path = os.path.normpath(
        os.path.join(__file__, "../../test_reporters/output_files/markdown_escape_output.html")
    )
    check_all(module_name=script_path, output=output_path)

    with open(output_path, "r") as output_file:

        response_body = output_file.read()
        cleaned_body = clean_response_body(response_body)

        assert ESCAPED_MARKDOWN in cleaned_body
        assert UNESCAPED_MARKDOWN not in cleaned_body

        snapshot.assert_match(cleaned_body, "markdown_escape.html")
