"""Tests for source-position conversions."""

from python_ta.util.source_positions import (
    message_column_to_codepoint,
    message_column_to_utf16,
    utf8_offset_to_codepoint,
    utf8_offset_to_utf16,
)


def test_utf8_offset_conversions() -> None:
    """Test conversions where UTF-8, code-point, and UTF-16 offsets differ."""
    line = 'text = "é😀"; unused = 1'
    byte_offset = len(line[: line.index("unused")].encode("utf-8"))

    assert utf8_offset_to_codepoint(line, byte_offset) == 13
    assert utf8_offset_to_utf16(line, byte_offset) == 14


def test_pycodestyle_column_conversion() -> None:
    """Test conversion of pycodestyle's Unicode code-point columns."""
    line = 'text = "😀"; target = 1'
    target_index = line.index("target")

    assert message_column_to_codepoint(line, target_index, "pep8-errors") == target_index
    assert message_column_to_utf16(line, target_index, "pep8-errors") == 13
