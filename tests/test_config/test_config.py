"""
Test suite for checking whether configuration worked correctly with user-inputted configurations.
"""
import os

import pytest

import python_ta

TEST_CONFIG = {
    "pyta-number-of-messages": 10,
    "max-nested-blocks": 5,
    "max-line-length": 120,
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
