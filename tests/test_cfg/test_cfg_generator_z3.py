"""
Test suite for generating z3 control flow graphs using the PythonTA API.
"""

import os.path
from unittest.mock import patch

import pytest

import python_ta.cfg.cfg_generator as cfg_generator


@pytest.fixture
def create_cfg_z3():
    """Create the CFG for each test that uses the code in a file fixture."""
    # Setup: store the paths of the files being used/created
    script_name = "file_fixtures/my_file.py"
    dot_file_path = os.path.splitext(os.path.basename(script_name))[0] + ".gv"
    svg_file_path = dot_file_path[:-3] + ".svg"

    # Create the graphviz files using my_file.py
    cfg_generator.generate_cfg(mod=script_name, auto_open=False, z3_enabled=True)

    # Open the actual graphviz file for reading
    gv_file_io = open(dot_file_path)

    yield dot_file_path, svg_file_path, gv_file_io

    # Teardown: close any open file IO and remove the graphviz generated files
    gv_file_io.close()
    os.remove(dot_file_path)
    os.remove(svg_file_path)


def test_cfg_z3_enabled(snapshot, create_cfg_z3) -> None:
    """Test verifies that `generate_cfg` correctly creates a graphviz dot file with the expected content when z3
    enabled."""
    _, _, gv_file_io = create_cfg_z3

    # Check that the contents match with the snapshot
    snapshot.snapshot_dir = "snapshots"
    snapshot.assert_match(gv_file_io.read(), "my_file.gv")
