"""Tests for top level __init__.py logging functionality in pyta"""
import python_ta


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

    # Checking indentation error (Use unexpected indent) # TODO does pyta handle these erros
    python_ta.check_all(module_name="examples/syntax_errors/unexpected_indent")
    assert "indentation error at line" in caplog.text

    # Checking token error (Use syntax error examples)
    python_ta.check_all(module_name="examples/syntax_errors/missing_colon")
    assert "syntax error in your file" in caplog.text

    # Checking unicode decode error


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
