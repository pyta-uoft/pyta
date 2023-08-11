"""
Test suite for generating control flow graphs using the PythonTA API.
"""
import os.path

import pytest

import python_ta.cfg.cfg_generator as cfg_generator


@pytest.fixture(autouse=True)
def reset_dir(request, monkeypatch):
    """Reset the current working directory after each test."""
    monkeypatch.chdir(request.fspath.dirname)


@pytest.fixture
def create_cfg():
    """Create the CFG for each test that uses the code in a file fixture."""
    # Setup: store the paths of the files being used/created
    script_name = "file_fixtures/my_file.py"
    dot_file_path = os.path.splitext(os.path.basename(script_name))[0]
    svg_file_path = dot_file_path + ".svg"

    # Create the graphviz files using my_file.py
    cfg_generator.generate_cfg(mod=script_name, auto_open=False)

    # Open the actual graphviz file for reading
    gv_file_io = open(dot_file_path)

    yield dot_file_path, svg_file_path, gv_file_io

    # Teardown: close any open file IO and remove the graphviz generated files
    gv_file_io.close()
    os.remove(dot_file_path)
    os.remove(svg_file_path)


@pytest.fixture
def create_cfg_funcs_only():
    """Create a CFG for each test that uses the code in a file fixture.

    This fixture specifies that cfgs will only be created for functions.
    """
    # Setup: store the paths of the files being used/created
    script_name = "file_fixtures/funcs_only.py"
    dot_file_path = os.path.splitext(os.path.basename(script_name))[0]
    svg_file_path = dot_file_path + ".svg"

    # Create the graphviz files using my_file.py
    options = {
        "functions": ["MyClass.foo", "foo", "hoo"],
    }
    cfg_generator.generate_cfg(mod=script_name, auto_open=False, visitor_options=options)

    # Open the actual graphviz file for reading
    gv_file_io = open(dot_file_path)

    yield dot_file_path, svg_file_path, gv_file_io

    # Teardown: close any open file IO and remove the graphviz generated files
    gv_file_io.close()
    os.remove(dot_file_path)
    os.remove(svg_file_path)


def test_script_external_call(create_cfg) -> None:
    """Test that generate_cfg correctly creates both graph files when the script does not contain
    the call to create its control flow graph."""
    # Receive the file paths from the setup_files fixture
    dot_file_path, svg_file_path, _ = create_cfg

    # Check if the graphviz files were created
    assert os.path.isfile(dot_file_path)
    assert os.path.isfile(svg_file_path)


def test_script_output_with_snapshot(snapshot, create_cfg) -> None:
    """Test that generate_cfg correctly creates a graphviz dot file with the expected content."""
    # Receive the file paths from the setup_files fixture
    _, _, gv_file_io = create_cfg

    # Check that the contents match with the snapshot
    snapshot.snapshot_dir = "snapshots"
    snapshot.assert_match(gv_file_io.read(), "my_file.gv")


def test_file_creation_funcs_only(snapshot, create_cfg_funcs_only) -> None:
    """Test that generate_cfg correctly creates both graph files when the script does not contain
    the call to create its own cfg.

    The call to generate_cfg specifies to only create cfgs for functions.
    """
    # Receive the file paths from the setup_files fixture
    dot_file_path, svg_file_path, _ = create_cfg_funcs_only

    # Check if the graphviz files were created
    assert os.path.isfile(dot_file_path)
    assert os.path.isfile(svg_file_path)


def test_file_output_with_snapshot_funcs_only(snapshot, create_cfg_funcs_only) -> None:
    """Test that generate_cfg correctly creates a graphviz dot file with the expected content when
    specified to only create cfgs for functions."""
    _, _, gv_file_io = create_cfg_funcs_only

    # Check that the contents match with the snapshot
    snapshot.snapshot_dir = "snapshots"
    snapshot.assert_match(gv_file_io.read(), "funcs_only.gv")


def test_mod_not_valid(capsys) -> None:
    """Test that generate_cfg prints the correct error message when `mod` is not a valid file.

    No files will be created (so no cleanup is required). Uses the `capsys` fixture to access
    stdout.
    """
    script_name = "not a valid file"
    expected = "Could not find the file called, `not a valid file`\n\n"

    cfg_generator.generate_cfg(mod=script_name, auto_open=False)

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

    cfg_generator.generate_cfg(mod=script_name, auto_open=False)

    captured = capsys.readouterr()

    assert captured.out == expected
