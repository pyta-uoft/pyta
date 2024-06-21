"""
Contains tests for the black formatting tool integration to python_ta.check_all.
"""

import contextlib
import io
import subprocess
import sys

import pytest

error_params = [
    (
        """def foo():print("Hello, world!")\nimport python_ta\npython_ta.check_all(autoformat=True)""",
        True,
        """def foo():\n    print("Hello, world!")\n\n\nimport python_ta\n\npython_ta.check_all(autoformat=True)\n""",
    ),
    (
        """def foo():print("Hello, world!")\nimport python_ta\npython_ta.check_all(autoformat=True, config={'max-line-length': 50})""",
        True,
        """def foo():\n    print("Hello, world!")\n\n\nimport python_ta\n\npython_ta.check_all(\n    autoformat=True,\n    config={\'max-line-length\': 50},\n)\n""",
    ),
    (
        """def foo():print("Hello, world!")\nimport python_ta\npython_ta.check_all(autoformat=False)""",
        False,
        """def foo():print("Hello, world!")\nimport python_ta\npython_ta.check_all(autoformat=False)""",
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


@pytest.mark.parametrize("source, pep8_check, expected_code", error_params)
def test_black_formatting(source, pep8_check, expected_code, unformatted_file):
    output = io.StringIO()

    with contextlib.redirect_stdout(output):
        result = subprocess.run(
            [
                sys.executable,
                unformatted_file,
            ],
        )

    # Check for pep8_errors in reporter
    if pep8_check:
        num_pep8 = output.getvalue().count('"symbol": "pep8-errors"')
        assert num_pep8 == 0, f"Expected:\n{0}\nBut got:\n{num_pep8}"

    # Check black ran successfully
    assert result.returncode == 0, f"Black failed with {result.stderr}"

    # Check if black formatted the file correctly
    with open(unformatted_file, "r") as f:
        formatted_code = f.read()

    assert (
        formatted_code == expected_code
    ), f"Expected:\n{expected_code}\nBut got:\n{formatted_code}"
