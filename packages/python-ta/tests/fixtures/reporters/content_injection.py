"""This script serves as the entry point for the PyTA HTML reporter tests.
It is invoked by the test `tests/test_reporters/test_html_reporter::test_injection()`
to ensure that no HTML can be injected into the HTML report."""

def inject_script():
    a = "hello"
    x = f'{a + "<script>alert(2);</script>"}'
    return x