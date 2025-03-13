import subprocess
import sys
from os import environ


def test_valid_message_config_and_pyta_overwrite():
    """Test the error messages given a valid messages-config-path with use-pyta-error-messages as True"""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_user_config_pyta_overwrite.pylintrc",
            "tests/test_messages_config/testing_code.py",
        ],
        capture_output=True,
        text=True,
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert "This custom error message is modified." in output.stdout
    assert "The first reversed() argument is not a sequence" not in output.stdout


def test_no_message_config_and_pyta_overwrite():
    """Test the error messages without a messages-config-path with use-pyta-error-messages as True"""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_no_user_config_pyta_overwrite.pylintrc",
            "tests/test_messages_config/testing_code.py",
        ],
        capture_output=True,
        text=True,
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert "This custom error message is modified." not in output.stdout
    assert "The first reversed() argument is not a sequence" not in output.stdout


def test_valid_message_config_and_no_pyta_overwrite():
    """Test the error messages given a valid messages-config-path with use-pyta-error-messages as False"""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_user_config_no_pyta_overwrite.pylintrc",
            "tests/test_messages_config/testing_code.py",
        ],
        capture_output=True,
        text=True,
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert "This custom error message is modified." in output.stdout
    assert "The first reversed() argument is not a sequence" in output.stdout


def test_no_message_config_and_no_pyta_overwrite():
    """Test the error messages without a messages-config-path with use-pyta-error-messages as False"""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_no_user_config_no_pyta_overwrite.pylintrc",
            "tests/test_messages_config/testing_code.py",
        ],
        capture_output=True,
        text=True,
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert "This custom error message is modified." not in output.stdout
    assert "The first reversed() argument is not a sequence" in output.stdout


def test_valid_message_config_no_section_header_and_pyta_overwrite():
    """Test the error messages given a valid messages-config-path with no section headers
    and use-pyta-error-messages as True.
    """
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_user_config_no_section_header_pyta_overwrite.pylintrc",
            "tests/test_messages_config/testing_code.py",
        ],
        capture_output=True,
        text=True,
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert "This custom error message is modified." in output.stdout
    assert "The first reversed() argument is not a sequence" not in output.stdout


def test_valid_message_config_no_section_header_and_no_pyta_overwrite():
    """Test the error messages given a valid messages-config-path with no section headers
    and use-pyta-error-messages as False."""
    output = subprocess.run(
        [
            sys.executable,
            "-m",
            "python_ta",
            "--config",
            "tests/test_messages_config/test_user_config_no_section_header_no_pyta_overwrite.pylintrc",
            "tests/test_messages_config/testing_code.py",
        ],
        capture_output=True,
        text=True,
        env={**environ, "PYTHONIOENCODING": "utf-8"},
    )

    assert "This custom error message is modified." in output.stdout
    assert "The first reversed() argument is not a sequence" in output.stdout
