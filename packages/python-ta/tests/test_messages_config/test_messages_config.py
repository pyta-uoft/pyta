import io
import logging
import os

import pytest

import python_ta

TEST_DIR = os.path.dirname(__file__)


@pytest.fixture
def output() -> None:
    """Create a StringIO object to be passed into the output argument of the check function."""
    output = io.StringIO()
    yield output
    output.close()


def test_valid_message_config_and_pyta_overwrite(output: io.StringIO):
    """Test the error messages given a valid messages-config-path with use-pyta-error-messages as True"""
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(TEST_DIR, "test_user_config_pyta_overwrite.pylintrc"),
        output=output,
    )

    assert "This custom error message is modified." in output.getvalue()
    assert "The first reversed() argument is not a sequence" not in output.getvalue()


def test_no_message_config_and_pyta_overwrite(output: io.StringIO):
    """Test the error messages without a messages-config-path with use-pyta-error-messages as True"""
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(TEST_DIR, "test_no_user_config_pyta_overwrite.pylintrc"),
        output=output,
    )

    assert "This custom error message is modified." not in output.getvalue()
    assert "The first reversed() argument is not a sequence" not in output.getvalue()


def test_valid_message_config_and_no_pyta_overwrite(output: io.StringIO):
    """Test the error messages given a valid messages-config-path with use-pyta-error-messages as False"""
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(TEST_DIR, "test_user_config_no_pyta_overwrite.pylintrc"),
        output=output,
    )

    assert "This custom error message is modified." in output.getvalue()
    assert "The first reversed() argument is not a sequence" in output.getvalue()


def test_no_message_config_and_no_pyta_overwrite(output: io.StringIO):
    """Test the error messages without a messages-config-path with use-pyta-error-messages as False"""
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(TEST_DIR, "test_no_user_config_no_pyta_overwrite.pylintrc"),
        output=output,
    )

    assert "This custom error message is modified." not in output.getvalue()
    assert "The first reversed() argument is not a sequence" in output.getvalue()


def test_valid_message_config_no_section_header_and_pyta_overwrite(output: io.StringIO):
    """Test the error messages given a valid messages-config-path with no section headers
    and use-pyta-error-messages as True.
    """
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(TEST_DIR, "test_user_config_no_section_header_pyta_overwrite.pylintrc"),
        output=output,
    )

    assert "This custom error message is modified." in output.getvalue()
    assert "The first reversed() argument is not a sequence" not in output.getvalue()


def test_valid_message_config_no_section_header_and_no_pyta_overwrite(
    output: io.StringIO,
):
    """Test the error messages given a valid messages-config-path with no section headers
    and use-pyta-error-messages as False.
    """
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(
            TEST_DIR, "test_user_config_no_section_header_no_pyta_overwrite.pylintrc"
        ),
        output=output,
    )

    assert "This custom error message is modified." in output.getvalue()
    assert "The first reversed() argument is not a sequence" in output.getvalue()


def test_valid_message_config_no_section_header_and_incorrect_error_message(
    output: io.StringIO, caplog
):
    """Test the error messages given a valid messages-config-path with no section headers
    and use-pyta-error-messages as True.
    """
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(
            TEST_DIR,
            "test_user_config_no_section_header_incorrect_error_message.pylintrc",
        ),
        output=output,
    )

    assert "This custom error message is modified." in output.getvalue()
    assert "The first reversed() argument is not a sequence" not in output.getvalue()
    assert (
        "root",
        logging.WARNING,
        "A1234 is not a valid error id.",
    ) in caplog.record_tuples


def test_valid_message_config_incorrect_section_header(output: io.StringIO):
    """Test the error messages given a valid messages-config-path with incorrectly defined section headers
    and use-pyta-error-messages as True. The error messages should still be overridden correctly as
    all section headers are ignored.
    """
    python_ta.check_all(
        os.path.join(TEST_DIR, "testing_code.py"),
        config=os.path.join(TEST_DIR, "test_user_config_incorrect_section_header.pylintrc"),
        output=output,
    )

    assert "This custom error message is modified." in output.getvalue()
    assert "The first reversed() argument is not a sequence" not in output.getvalue()
