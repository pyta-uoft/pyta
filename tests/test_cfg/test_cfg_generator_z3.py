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
    file_path = "../../examples/pylint/r0912_too_many_branches.py"
    gv_file_path = "r0912_too_many_branches.gv"
    svg_file_path = "r0912_too_many_branches.svg"

    # Create the graphviz files using my_file.py
    cfg_generator.generate_cfg(mod=file_path, z3_enabled=True)

    # # Open the actual graphviz file for reading
    gv_file_io = open(gv_file_path)

    assert gv_file_path in gv_file_io.read()

    # Teardown: close any open file IO and remove the graphviz generated files
    gv_file_io.close()
    os.remove(gv_file_path)
    os.remove(svg_file_path)
