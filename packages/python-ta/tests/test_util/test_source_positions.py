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


def test_checker_specific_column_encodings() -> None:
    """Test normalization of the distinct column formats used by custom checkers."""
    line = 'text = "😀"; target = 1'
    target_index = line.index("target")
    mypy_start_column = len(line[:target_index].encode("utf-8")) + 1

    assert message_column_to_codepoint(line, target_index, "pep8-errors") == target_index
    assert (
        message_column_to_codepoint(line, mypy_start_column, "incompatible-assignment")
        == target_index
    )
    assert message_column_to_utf16(line, target_index, "pep8-errors") == 13
    assert message_column_to_utf16(line, mypy_start_column, "incompatible-assignment") == 13
