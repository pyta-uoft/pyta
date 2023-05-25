"""
Test suite for generating control flow graphs using the PythonTA API.
"""
import os.path

import pytest

import python_ta.cfg as cfg


@pytest.fixture(autouse=True)
def reset_dir(request, monkeypatch):
    """Reset the current working directory after each test."""
    monkeypatch.chdir(request.fspath.dirname)


def test_script_external_call() -> None:
    """Test that generate_cfg correctly creates both graph files when the script does not contain
    the call to create its control flow graph."""
    script_name = "file_fixtures/my_file.py"
    dot_file_path = os.path.splitext(os.path.basename(script_name))[0]
    svg_file_path = dot_file_path + ".svg"

    # Create the graphviz files using my_file.py
    cfg.generate_cfg(mod=script_name, auto_open=False)

    # Check if the graphviz files were created
    assert os.path.isfile(dot_file_path) and os.path.isfile(svg_file_path)

    # Teardown: remove the graphviz generated files
    os.remove(dot_file_path)
    os.remove(svg_file_path)


def test_script_output_with_snapshot(snapshot) -> None:
    """Test that generate_cfg correctly creates a graphviz dot file with the expected content."""
    script_name = "file_fixtures/my_file.py"
    dot_file_path = os.path.splitext(os.path.basename(script_name))[0]
    svg_file_path = dot_file_path + ".svg"

    # Create the graphviz files using my_file.py
    cfg.generate_cfg(mod=script_name, auto_open=False)

    # Open the actual graphviz file for reading
    actual = open(dot_file_path, "r")

    # Check that the contents match
    snapshot.snapshot_dir = "snapshots"
    snapshot.assert_match(actual.read(), "sample_cfg_output.txt")

    # Teardown: close any open files and remove the graphviz generated files
    actual.close()
    os.remove(dot_file_path)
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
