"""This script serves as the entry point for the PyTA HTML reporter tests
It is invoked by the test `tests/test_reporters/test_html_reporter::test_markdown_escape()`
to ensure that any markdown characters from the user's code are properly escaped before being rendered."""
def markdown_chars():
    y = "hello"
    z = f'{y + "` ##world `"}'

