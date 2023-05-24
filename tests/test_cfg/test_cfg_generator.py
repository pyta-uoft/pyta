"""
Test suite for generating control flow graphs using the PythonTA API.
"""
import os.path
import tempfile
from typing import Tuple

import pytest

import python_ta.cfg as cfg

TEST_SCRIPT = """
def foo() -> None:
    for i in range(1, 10):
        if i < 5:
            print("hi")
"""

HOME_DIRECTORY = os.getcwd()


@pytest.fixture(autouse=True)
def reset_dir(request, monkeypatch):
    """Reset the current working directory after each test."""
    monkeypatch.chdir(request.fspath.dirname)


def create_script(code: str) -> Tuple[str, str, str]:
    """Returns a 3-tuple containing the name of the temporary file corresponding to the Python file
    of script, and the names of the two files that will be produced by graphviz."""
    script = tempfile.NamedTemporaryFile(suffix=".py", mode="w+t", delete=False)
    script.writelines(code)
    script.flush()
    script.close()

    # Get the paths of the files of interest (temp file + graphviz files that will be created)
    dir_name = os.path.dirname(script.name)
    file_path = os.path.splitext(script.name)[0]
    svg_file_path = file_path + ".svg"

    # Change directory to the temporary directory so the graphviz files will be created there
    os.chdir(dir_name)

    return script.name, file_path, svg_file_path


def test_script_external_call() -> None:
    """Test that generate_cfg correctly creates both graph files when the script does not contain
    the call to create its control flow graph."""
    # Create the temporary file and store the name of it and the file paths of the graphviz files
    script_name, file_path, svg_file_path = create_script(TEST_SCRIPT)

    cfg.generate_cfg(mod=script_name, auto_open=False)

    # Check if the graphviz files were created
    assert os.path.isfile(file_path) and os.path.isfile(svg_file_path)

    # Teardown: remove the temporary files
    os.remove(script_name)
    os.remove(file_path)
    os.remove(svg_file_path)


def test_script_output_with_snapshot(snapshot) -> None:
    """Test that generate_cfg correctly creates a graphviz file with the expected content."""
    # Create the temporary file and store the name of it and the file paths of the graphviz files
    script_name, file_path, svg_file_path = create_script(TEST_SCRIPT)

    # Create the graphviz files
    cfg.generate_cfg(mod=script_name, auto_open=False)

    # Open the actual graphviz file for reading
    actual = open(file_path, "r")
    # Skip the first line since it depends on the file name
    next(actual)

    # Check that the contents match
    snapshot.snapshot_dir = HOME_DIRECTORY + "\\tests\\test_cfg\\snapshots"
    snapshot.assert_match(actual.read(), "sample_cfg_output.txt")

    # Teardown: close any open files and remove the temporary files
    actual.close()
    os.remove(script_name)
    os.remove(file_path)
    os.remove(svg_file_path)


def test_mod_not_valid(capsys) -> None:
    """Test that generate_cfg prints the correct error message when `mod` is not a valid file.

    No files will be created (so no cleanup is required). Uses the `capsys` fixture to access
    stdout.
    """
    script_name = "not a valid file"
    expected = "Could not find the file called, `not a valid file`\n\n"

    cfg.generate_cfg(mod=script_name, auto_open=False)

    captured = capsys.readouterr()

    assert captured.out == expected


def test_mod_not_str(capsys) -> None:
    """Test that generate_cfg enforces `mod` to be of type str and prints the correct error message
    when it isn't.

    No files will be created (so no cleanup is required). Uses the `capsys` fixture to access
    stdout.
    """
    script_name = 1
    expected = "No CFG generated. Input to check, `1`, has invalid type, must be a string.\n"

    cfg.generate_cfg(mod=script_name, auto_open=False)

    captured = capsys.readouterr()

    assert captured.out == expected
