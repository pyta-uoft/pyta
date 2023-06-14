"""
Test suite for checking whether configuration worked correctly with user-inputted configurations.
"""
import os

import pytest

import python_ta


@pytest.fixture
def configure_linter():
    """Create a linter using the default python_ta config settings and override using the expected
    final config options in the test.pylintrc file."""
    config = {
        "pyta-number-of-messages": 10,
        "max-nested-blocks": 5,
        "max-line-length": 120,
    }
    linter = python_ta.reset_linter()

    for key in config:
        linter.set_option(key, config[key])

    yield linter


def test_user_config_dict(configure_linter) -> None:
    """Test that reset_linter correctly overrides the default options when the user provides a
    config of type dict."""
    config = {
        "pyta-number-of-messages": 10,
        "max-nested-blocks": 5,
        "max-line-length": 120,
    }
    expected = configure_linter.config.__dict__
    actual = python_ta.reset_linter(config=config).config.__dict__

    assert actual == expected


def test_user_config_file(configure_linter) -> None:
    """Test that reset_linter correctly overrides the default options when the user provides a
    config file of type str (so it is a file)."""
    curr_dir = os.path.dirname(__file__)
    config = os.path.join(curr_dir, "file_fixtures", "test.pylintrc")
    expected = configure_linter.config.__dict__
    actual = python_ta.reset_linter(config=config).config.__dict__

    assert actual == expected
