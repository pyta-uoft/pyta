import pytest

from python_ta import check_all

config = {
    "messages-config-path": "tests/test.messages_config.toml",
    "output-format": "python_ta.reporters.PlainReporter",
}


def test_modified_message(capfd):
    check_all("examples/pylint/e0111_bad_reversed_sequence.py", config)
    out, err = capfd.readouterr()
    assert "This custom error message is modified." in out


def test_default_message(capfd):
    check_all("examples/pylint/w0101_unreachable.py", config)
    out, err = capfd.readouterr()
    assert (
        "Code after a return or raise statement will never be run, so you should either remove this code or review the above return/raise statement(s)."
        in out
    )
