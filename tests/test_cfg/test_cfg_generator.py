"""
Test suite for generating control flow graphs using the PythonTA API.
"""
import os.path
import subprocess
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

TEST_SCRIPT_WITH_IMPORT = (
    TEST_SCRIPT
    + """
if __name__ == "__main__":
    import python_ta.cfg
    python_ta.cfg.generate_cfg(auto_open=False)
"""
)


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


def test_script_internal_call() -> None:
    """Test that generate_cfg correctly creates both graph files when the script contains the call
    to create its control flow graph."""
    # Create the temporary file and store the name of it and the file paths of the graphviz files
    script_name, file_path, svg_file_path = create_script(TEST_SCRIPT_WITH_IMPORT)

    # Execute the script, which contains the call to generate the control flow graph
    subprocess.run(["python", script_name])

    # Check if the graphviz files were created
    assert os.path.isfile(file_path) and os.path.isfile(svg_file_path)

    # Teardown: remove the temporary files
    os.remove(script_name)
    os.remove(file_path)
    os.remove(svg_file_path)
