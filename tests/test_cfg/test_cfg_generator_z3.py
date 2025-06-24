"""
Test suite for generating z3 control flow graphs using the PythonTA API.
"""

import os.path
from unittest.mock import patch

import pytest

import python_ta.cfg.cfg_generator as cfg_generator


def test_cfg_z3_enabled() -> None:
    """Test verifies that `generate_cfg` correctly creates a graphviz dot file with the expected content when z3
    enabled."""
    script_name = "file_fixtures/my_file.py"
    dot_file_path = os.path.splitext(os.path.basename(script_name))[0] + ".gv"
    svg_file_path = dot_file_path[:-3] + ".svg"

    # Create the graphviz files using my_file.py
    cfg_generator.generate_cfg(mod=script_name, auto_open=False, z3_enabled=True)

    # Open the actual graphviz file for reading
    gv_file_io = open(dot_file_path)

    assert "my_file.gv" in gv_file_io.read()

    # Teardown: close any open file IO and remove the graphviz generated files
    gv_file_io.close()
    os.remove(dot_file_path)
    os.remove(svg_file_path)
