"""
Test suite for checking that the correct number of error occurrences are being displayed.
"""

import contextlib
import io
import os

from python_ta import check_all


def pyta_output(num_msgs: int) -> str:
    """Returns the PythonTA report as a string."""
    output = io.StringIO()

    curr_dir = os.path.dirname(__file__)
    test_file = os.path.join(curr_dir, "file_fixtures", "funcs_with_errors.py")

    with contextlib.redirect_stdout(output):
        check_all(
            module_name=test_file,
            config={
                "pyta-number-of-messages": num_msgs,
                "output-format": "python_ta.reporters.JSONReporter",
            },
        )

    return output.getvalue()


def test_default() -> None:
    """Tests that all messages are displayed when pyta-number-of-messages = 0."""
    pyta_report = pyta_output(0)
    expected = 12
    actual = pyta_report.count("msg_id")

    assert expected == actual


def test_num_msgs2() -> None:
    """Tests that only two messages per error are displayed when pyta-number-of-messages = 2."""
    pyta_report = pyta_output(2)
    expected = 7
    actual = pyta_report.count("msg_id")

    assert expected == actual


def test_num_msgs_greater() -> None:
    """Tests that all messages are displayed when pyta-number-of-messages is greater than the number of errors."""
    pyta_report = pyta_output(5)
    expected = 12
    actual = pyta_report.count("msg_id")

    assert expected == actual
