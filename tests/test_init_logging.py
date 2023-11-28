"""Tests for top level __init__.py logging functionality in pyta"""
from unittest.mock import patch

import python_ta
from python_ta import _get_valid_files_to_check, _verify_pre_check


def test_check_log(caplog) -> None:
    """Testing logging in _check function when no exception is thrown"""
    expected_messages = [
        "was checked using the configuration file:",
        "was checked using the messages-config file:",
    ]

    python_ta._check()
    for i in range(2):
        assert caplog.records[i].levelname == "INFO"
        assert expected_messages[i] in caplog.records[i].msg


@patch("python_ta._get_valid_files_to_check", side_effect=Exception("Testing"))
def test_check_exception_log(_, caplog) -> None:
    """Testing logging in _check function when exception is thrown"""
    try:
        python_ta._check()
    except Exception:
        expected_logs = [
            "Unexpected error encountered! Please report this to your instructor (and attach the code that caused the error).",
            "Error message: \"Testing\"",
        ]

        for i in range(2):
            assert caplog.records[i].levelname == "ERROR"
            assert expected_logs[i] in caplog.records[i].msg


@patch("pylint.utils.pragma_parser.OPTION_PO.search", side_effect=IndentationError)
def test_pre_check_log(_, caplog) -> None:
    """Testing logging in _verify_pre_check function"""


def test_get_valid_files_to_check(caplog) -> None:
    """Testing logging in _get_valid_files_to_check function"""
    expected_logs = [
        "No checks run. Input to check, `{'examples/nodes/assign'}`, has invalid type, must be a list of strings.",
        "No check run on file `0`, with invalid type. Must be type: str.",
        "Could not find the file called, `foo`",
    ]

    # Iterating through generators to produce errors
    [_ for _ in _get_valid_files_to_check(module_name={"examples/nodes/assign"})]
    [_ for _ in _get_valid_files_to_check(module_name=[0])]
    [_ for _ in _get_valid_files_to_check(module_name="foo")]

    for i in range(len(expected_logs)):
        assert caplog.records[i].levelname == "ERROR"
        assert expected_logs[i] in caplog.records[i].msg


def test_doc_log(caplog) -> None:
    """Testing logging in doc function"""
    python_ta.doc("E0602")
    assert caplog.records[0].levelname == "INFO"
    assert (
        "Opening http://www.cs.toronto.edu/~david/pyta/checkers/index.html#e0602 in a browser."
        in caplog.text
    )
