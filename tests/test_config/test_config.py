"""
Test suite for checking whether configuration worked correctly with user-inputted configurations.
"""
import json
import os
from unittest.mock import mock_open, patch

import pytest

import python_ta

TEST_CONFIG = {
    "pyta-number-of-messages": 10,
    "max-nested-blocks": 5,
    "max-line-length": 120,
}

# Non-fatal config errors. Fatal errors will be checked individually.
CONFIG_ERRORS_TO_CHECK = {
    "W0012",
    "R0022",
    "E0015",
}


@pytest.fixture
def configure_linter_load_default():
    """Create a linter using the default PythonTA config settings and override using the expected
    final config options in the test.pylintrc file."""
    linter = python_ta.reset_linter()

    for key in TEST_CONFIG:
        linter.set_option(key, TEST_CONFIG[key])

    yield linter


@pytest.fixture
def configure_linter_no_default():
    """Create a linter without loading the default PythonTA config settings and override using the
    expected final config options in the test.pylintrc file."""
    linter = python_ta.reset_linter(load_default_config=False)

    for key in TEST_CONFIG:
        linter.set_option(key, TEST_CONFIG[key])

    yield linter


def test_user_config_dict(configure_linter_load_default) -> None:
    """Test that reset_linter correctly overrides the default options when the user provides a
    config of type dict."""
    expected = configure_linter_load_default.config.__dict__
    actual = python_ta.reset_linter(config=TEST_CONFIG).config.__dict__

    assert actual == expected


def test_user_config_file(configure_linter_load_default) -> None:
    """Test that reset_linter correctly overrides the default options when the user provides a
    config file of type str (so it is a file)."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test.pylintrc")
    expected = configure_linter_load_default.config.__dict__
    actual = python_ta.reset_linter(config=config).config.__dict__

    assert actual == expected


def test_user_config_dict_no_default(configure_linter_no_default) -> None:
    """Test that reset_linter correctly overrides the default options when the user provides a
    config of type dict.

    The default options are not loaded from the PythonTA default config."""
    expected = configure_linter_no_default.config.__dict__
    actual = python_ta.reset_linter(config=TEST_CONFIG, load_default_config=False).config.__dict__

    assert actual == expected


def test_user_config_file_no_default(configure_linter_no_default) -> None:
    """Test that reset_linter correctly overrides the default options when the user provides a
    config file of type str (so it is a file).

    The default options are not loaded from the PythonTA default config."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test.pylintrc")
    expected = configure_linter_no_default.config.__dict__
    actual = python_ta.reset_linter(config=config, load_default_config=False).config.__dict__

    assert actual == expected


def test_checker_options_in_no_default(configure_linter_no_default) -> None:
    """Test that reset_linter correctly applies PythonTA's default option values specified in the
    codebase (not from the config file). Note, not all of the default option values are checked.

    The default options are not loaded from the PythonTA default config."""
    options_dict = configure_linter_no_default.config.__dict__
    pyta_checker_options = (
        "pyta_type_check",
        "pyta_number_of_messages",
        "pyta_template_file",
        "pyta_error_permission",
        "pyta_file_permission",
        "pyta_server_address",
        "messages_config_path",
    )

    assert all(option in options_dict for option in pyta_checker_options)


def test_default_pylint_checks_in_no_default(configure_linter_no_default) -> None:
    """Test that reset_linter correctly does not load PythonTA's default config options by checking
    that the previously disabled pylint checks are no longer disabled.

    Note that not all of the previously disabled pylint checks are checked."""
    disabled_checks = configure_linter_no_default.config.__dict__["disable"]
    previously_disabled_checks = (
        "lambda-expressions",
        "similarities",
        "spelling",
        "threading",
        "unnecessary-dunder-call",
        "unsupported_version",
        "missing-timeout",
        "positional-only-arguments-expected",
    )

    assert all(
        check not in disabled_checks for check in previously_disabled_checks if disabled_checks
    )


def test_config_parsing_errors() -> None:
    """Test that the configuration options gets overridden without error when there are errors
    parsing the config files.

    This checks the non-fatal errors from parsing the config file."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_with_errors.pylintrc")
    reporter = python_ta.reset_linter(config=config).reporter

    # Check if there are messages with `msg_id`s from CONFIG_ERRORS_TO_CHECK.
    message_ids = [msg.msg_id for message_lis in reporter.messages.values() for msg in message_lis]

    assert all(error in message_ids for error in CONFIG_ERRORS_TO_CHECK)


def test_config_parsing_errors_no_default() -> None:
    """Test that the configuration options gets loaded without error when there are errors
    parsing the config files.

    This checks the non-fatal errors from parsing the config file.

    The default options are not loaded from the PythonTA default config."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_with_errors.pylintrc")
    reporter = python_ta.reset_linter(config=config, load_default_config=False).reporter

    # Check if there are messages with `msg_id`s from CONFIG_ERRORS_TO_CHECK.
    message_ids = [msg.msg_id for message_lis in reporter.messages.values() for msg in message_lis]

    assert all(error in message_ids for error in CONFIG_ERRORS_TO_CHECK)


def test_json_config_parsing_error(capsys) -> None:
    """Test that the JSONReporter correctly includes the config parsing error in its report."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_json_with_errors.pylintrc")
    python_ta.check_all(module_name="examples/nodes/name.py", config=config)
    out = capsys.readouterr().out

    reports = json.loads(out)

    assert any(msg["msg_id"] == "W0012" for report in reports for msg in report["msgs"])


def test_print_messages_config_parsing_error(capsys) -> None:
    """Test that print_messages correctly prints the config parsing error in its report.

    This tests the functionality of PlainReporter and ColorReporter to verify it correctly includes
    the config parsing error in its printed report."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_plain_with_errors.pylintrc")
    python_ta.check_all(module_name="examples/nodes/name.py", config=config)

    out = capsys.readouterr().out

    assert "W0012" in out


def test_no_snippet_for_config_parsing_errors() -> None:
    """Test that there is no snippet being built for errors that come from parsing the config file."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_with_errors.pylintrc")
    reporter = python_ta.check_all(module_name="examples/nodes/name.py", config=config)

    # Gather all the built code snippets for the `msg_id`s specified in CONFIG_ERRORS_TO_CHECK.
    snippets = [
        msg.snippet
        for message_lis in reporter.messages.values()
        for msg in message_lis
        if msg.msg_id in CONFIG_ERRORS_TO_CHECK
    ]

    assert all(snippet == "" for snippet in snippets)


def test_config_parse_error(capsys) -> None:
    """Test that F0011 (config-parse-error) correctly gets reported."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_f0011.pylintrc")
    reporter = python_ta.check_all(module_name="examples/nodes/name.py", config=config)

    msg_id = reporter.messages[config][0].msg_id

    assert msg_id == "F0011"


def test_config_parse_error_has_no_snippet() -> None:
    """Test that F0011 (config-parse-error) correctly gets reported with no code snippet."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test_f0011.pylintrc")
    reporter = python_ta.check_all(module_name="examples/nodes/name.py", config=config)

    snippet = reporter.messages[config][0].snippet

    assert snippet == ""


def test_allow_pylint_comments() -> None:
    """Test that checks whether the allow-pylint-comments configuration option works as expected when it is
    set to True"""

    with patch("python_ta.tokenize.open", mock_open(read_data="# pylint: disable")):
        result = python_ta._verify_pre_check("", allow_pylint_comments=True)

    assert result is True


def test_disallows_pylint_comments() -> None:
    """Test that checks whether the allow-pylint-comments configuration option works as expected when it is
    is set to False"""

    with patch("python_ta.tokenize.open", mock_open(read_data="# pylint: disable")):
        result = python_ta._verify_pre_check("", allow_pylint_comments=False)

    assert result is False
