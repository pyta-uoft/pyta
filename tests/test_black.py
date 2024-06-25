"""
Contains tests for the black formatting tool integration to python_ta.check_all.
"""

import contextlib
import io
import subprocess
import sys

import pytest

import python_ta
from python_ta import check_all

error_params = [
    (
        """def foo():print("Hello, world!")\n""",
        {"output-format": "python_ta.reporters.JSONReporter"},
        True,
        """def foo():\n    print("Hello, world!")\n""",
    ),
    (
        """def foo():print("Hello, world!" + "This line is too long and should be split by black.")""",
        {"output-format": "python_ta.reporters.JSONReporter", "max-line-length": 50},
        True,
        """def foo():\n    print(\n        "Hello, world!"\n        + "This line is too long and should be split by black."\n    )\n""",
    ),
    (
        """def foo():print("Hello, world!")\n""",
        {"output-format": "python_ta.reporters.JSONReporter"},
        False,
        """def foo():print("Hello, world!")\n""",
    ),
]


@pytest.fixture
@pytest.mark.parametrize("source", error_params)
def unformatted_file(tmp_path, source):
    # Create a temporary file with unformatted Python code
    file_path = tmp_path / "sample_code.py"
    with open(file_path, "w") as f:
        f.write(source)
    return file_path


@pytest.mark.parametrize("source, config, pep8_check, expected_code", error_params)
def test_black_formatting(source, config, pep8_check, expected_code, unformatted_file):
    output = io.StringIO()

    with contextlib.redirect_stdout(output):
        python_ta.check_all(str(unformatted_file), config=config, autoformat=pep8_check)

    # Check for pep8_errors in reporter
    if pep8_check:
        num_pep8 = output.getvalue().count('"symbol": "pep8-errors"')
        assert num_pep8 == 0, f"Expected:\n{0}\nBut got:\n{num_pep8}"

    # Check if black formatted the file correctly
    with open(unformatted_file, "r") as f:
        formatted_code = f.read()

    assert (
        formatted_code == expected_code
    ), f"Expected:\n{expected_code}\nBut got:\n{formatted_code}"
