"""Tests for Z3Parser in python_ta_z3."""

from astroid import extract_node
from python_ta_z3.z3_parser import Z3Parser


def test_z3_parser_assignment() -> None:
    assignment = "n = 2 + 3"

    node = extract_node(assignment)
    parser = Z3Parser()
    assert parser.parse(node) == 5
