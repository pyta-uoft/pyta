import subprocess
import sys


def test_modified_message():
    """Test the presence of modified custom message."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test.pylintrc",
            "examples/pylint/e0111_bad_reversed_sequence.py",
        ],
        capture_output=True,
        text=True,
    )

    assert "This custom error message is modified." in output.stdout


def test_default_message():
    """Test the presence of default custom message not present in new configuration file."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test.pylintrc",
            "examples/pylint/w0101_unreachable.py",
        ],
        capture_output=True,
        text=True,
    )

    assert (
        "Code after a return or raise statement will never be run, so you should either remove this code or review the above return/raise statement(s)."
        in output.stdout
    )


def test_not_modified_message():
    """Test the modified custom message is not present."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_not_overwritten.pylintrc",
            "examples/pylint/e0111_bad_reversed_sequence.py",
        ],
        capture_output=True,
        text=True,
    )

    assert "This custom error message is modified." not in output.stdout


def test_not_default_message():
    """Test the presence of default custom message is present in new configuration file."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_not_overwritten.pylintrc",
            "examples/pylint/w0101_unreachable.py",
        ],
        capture_output=True,
        text=True,
    )

    assert (
        "Code after a return or raise statement will never be run, so you should either remove this code or review the above return/raise statement(s)."
        not in output.stdout
    )
