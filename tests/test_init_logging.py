"""Tests for top level __init__.py logging functionality in pyta"""

import logging
import os
import sys
import tokenize
from unittest.mock import patch

import python_ta
from python_ta import _get_valid_files_to_check, _verify_pre_check


def test_check_log(caplog) -> None:
    """Testing logging in _check function when no exception is thrown"""
    expected_messages = [
        "was checked using the configuration file:",
        "was checked using the messages-config file:",
    ]

    caplog.set_level(logging.INFO)
    python_ta._check(
        module_name=os.path.join(os.path.dirname(__file__), "fixtures", "no_errors.py"),
        local_config={"output-format": "python_ta.reporters.PlainReporter"},
    )
    for i in range(2):
        assert caplog.records[i].levelname == "INFO"
        assert expected_messages[i] in caplog.records[i].msg


@patch("python_ta._get_valid_files_to_check", side_effect=Exception("Testing"))
def test_check_exception_log(_, caplog) -> None:
    """Testing logging in _check function when exception is thrown"""
    try:
        python_ta._check(local_config={"output-format": "python_ta.reporters.PlainReporter"})
    except Exception:
        expected_logs = [
            "Unexpected error encountered! Please report this to your instructor (and attach the code that caused the error).",
            'Error message: "Testing"',
        ]

        for i in range(2):
            assert caplog.records[i].levelname == "ERROR"
            assert expected_logs[i] in caplog.records[i].msg


def test_pre_check_log_pylint_comment(caplog) -> None:
    """Testing logging in _verify_pre_check function when checking for pyling comment"""
    path = os.path.join(os.path.dirname(__file__), "fixtures", "pylint_comment.py")
    _verify_pre_check(path, False)
    assert f'String "pylint:" found in comment. No check run on file `{path}' in caplog.text
    assert "ERROR" == caplog.records[0].levelname


@patch("python_ta.tokenize.open", side_effect=IndentationError)
def test_pre_check_log_indentation_error(_, caplog) -> None:
    """Testing logging in _verify_pre_check function IndentationError catch block"""
    # Don't need a valid file path since patching error into open function
    _verify_pre_check("", False)
    assert "python_ta could not check your code due to an indentation error at line" in caplog.text
    assert "ERROR" == caplog.records[0].levelname


@patch("python_ta.tokenize.open", side_effect=tokenize.TokenError)
def test_pre_check_log_token_error(_, caplog) -> None:
    """Testing logging in _verify_pre_check function TokenError catch block"""
    # Don't need a valid file path since patching error into open function
    _verify_pre_check("", False)
    assert "python_ta could not check your code due to a syntax error in your file." in caplog.text
    assert "ERROR" == caplog.records[0].levelname


@patch("python_ta.tokenize.open", side_effect=UnicodeDecodeError("", b"", 0, 0, ""))
def test_pre_check_log_pylint_unicode_error(_, caplog) -> None:
    """Testing logging in _verify_pre_check function UnicodeDecodeError catch block"""
    expected_logs = [
        "python_ta could not check your code due to an invalid character. Please check the following lines in your file and all characters that are marked with a �.",
        '  Line 1: "�"\n',
        '  Line 2: "�"\n',
        '  Line 5: "�"\n',
    ]

    path = os.path.join(os.path.dirname(__file__), "fixtures", "unicode_decode_error.py")
    _verify_pre_check(path, False)

    for i in range(len(expected_logs)):
        assert expected_logs[i] == caplog.records[i].msg
        assert "ERROR" == caplog.records[i].levelname


def test_get_valid_files_to_check(caplog) -> None:
    """Testing logging in _get_valid_files_to_check function"""
    expected_logs = [
        "No checks run. Input to check, `{'examples/nodes/assign'}`, has invalid type, must be a list of strings.",
        "No check run on file `0`, with invalid type. Must be type: str.",
        "Could not find the file called, `foo`",
    ]

    # Iterating through generators to produce errors
    tuple(_get_valid_files_to_check(module_name={"examples/nodes/assign"}))
    tuple(_get_valid_files_to_check(module_name=[0]))
    tuple(_get_valid_files_to_check(module_name="foo"))

    for i in range(len(expected_logs)):
        assert caplog.records[i].levelname == "ERROR"
        assert expected_logs[i] in caplog.records[i].msg


@patch("webbrowser.open", lambda _: None)
def test_doc_log(capsys) -> None:
    """Testing logging in doc function"""
    python_ta.doc("E0602")
    captured = capsys.readouterr()
    assert (
        "Opening http://www.cs.toronto.edu/~david/pyta/checkers/index.html#e0602 in a browser."
        in captured.out
    )
