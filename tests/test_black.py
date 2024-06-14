import subprocess
import sys

import pytest


@pytest.fixture
def unformatted_file(tmp_path):
    # Create a temporary file with unformatted Python code
    source = """def foo():print("Hello, world!")\nimport python_ta\npython_ta.check_all(autoformat=True)"""
    file_path = tmp_path / "sample_code.py"
    with open(file_path, "w") as f:
        f.write(source)
    return file_path


def test_black_formatting(unformatted_file):
    # Run the unformatted file, which runs python_ta.check_all(autoformat=True)
    result = subprocess.run(
        [
            sys.executable,
            unformatted_file,
        ],
        capture_output=True,
        text=True,
    )

    # check black ran successfully
    assert result.returncode == 0, f"Black failed with {result.stderr}"

    # Check if black formatted the file correctly
    with open(unformatted_file, "r") as f:
        formatted_code = f.read()

    expected_code = """def foo():\n    print("Hello, world!")\n\n\nimport python_ta\n\npython_ta.check_all(autoformat=True)\n"""

    assert (
        formatted_code == expected_code
    ), f"Expected:\n{expected_code}\nBut got:\n{formatted_code}"
