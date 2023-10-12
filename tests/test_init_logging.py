"""Tests for top level __init__.py logging functionality in pyta"""
import sys

import python_ta


# TODO if statement not catching sys.version_info (suspicion init.py and import statement)
def test_sys_version_log(caplog, monkeypatch) -> None:
    """Testing if message logged when system version is too low is correct"""
    monkeypatch.setattr(sys, "version_info", (0, 0, 0))

    python_ta.check_all()
    assert caplog.records[0].levelname == "WARNING"
    assert "You need Python 3.7 or later to run PythonTA." in caplog.text


# TODO how to get unexpected error?
def test_check_log(caplog) -> None:
    """Testing logging in _check function"""
    expected_messages = [
        "was checked using the configuration file:",
        "was checked using the messages-config file:",
    ]

    python_ta.check_all(module_name="examples/nodes/assign")
    for i in range(2):
        assert caplog.records[i].levelname == "INFO"
        assert expected_messages[i] in caplog.records[i].msg


def test_pre_check_log(caplog) -> None:
    """Testing logging in _verify_pre_check function"""
    # Checking pylint comment

    # Checking indentation error

    # Checking token error

    # Checking unicode decode error
    pass


def test_files_to_check_log(caplog) -> None:
    """Testing logging in _get_valid_files_to_check function"""
    expected_logs = [
        "No checks run. Input to check, `{'examples/nodes/assign'}`, has invalid type, must be a list of strings.",
        "No check run on file `0`, with invalid type. Must be type: str.",
        "Could not find the file called, `foo`",
    ]
    python_ta.check_all(module_name={"examples/nodes/assign"})
    python_ta.check_all(module_name=[0])
    python_ta.check_all(module_name="foo")

    for i in range(3):
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
