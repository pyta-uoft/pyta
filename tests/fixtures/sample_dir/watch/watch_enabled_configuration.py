"""This script serves as the entry point for an integration test of the _check watch mode.
It is invoked by the test `tests/test_reporters/test_html_server::test_open_html_in_browser_watch()`
to verify that the correct report is generated through multiple file changes."""

import python_ta


def blank_function() -> int:
    """blank"""
    count: int = "ten"
    return count


if __name__ == "__main__":
    python_ta.check_all(config={
        "output-format": "python_ta.reporters.PlainReporter",
        "watch": True,
    })
