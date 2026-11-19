"""Utilities for converting source-code positions between encoding schemes."""

# Messages emitted by PythonTA's mypy-backed StaticTypeChecker.
MYPY_MESSAGE_SYMBOLS = {
    "incompatible-argument-type",
    "incompatible-assignment",
    "list-item-type-mismatch",
    "unsupported-operand-types",
    "union-attr-error",
    "dict-item-type-mismatch",
}


def utf8_offset_to_codepoint(line: str, byte_offset: int) -> int:
    """Convert a zero-based UTF-8 byte offset into a Unicode code-point offset."""
    return len(line.encode("utf-8")[:byte_offset].decode("utf-8"))


def codepoint_offset_to_utf16(line: str, codepoint_offset: int) -> int:
    """Convert a zero-based Unicode code-point offset into a UTF-16 code-unit offset."""
    return len(line[:codepoint_offset].encode("utf-16-le")) // 2


def utf8_offset_to_utf16(line: str, byte_offset: int) -> int:
    """Convert a zero-based UTF-8 byte offset into a UTF-16 code-unit offset."""
    return codepoint_offset_to_utf16(line, utf8_offset_to_codepoint(line, byte_offset))


def message_column_to_codepoint(
    line: str, column: int, symbol: str, *, is_end: bool = False
) -> int:
    """Normalize a checker-specific message column to a Unicode code-point offset."""
    if symbol == "pep8-errors":
        return column

    # Mypy columns are one-based and inclusive, so only its start needs adjustment
    # when converting to a zero-based, end-exclusive range.
    if symbol in MYPY_MESSAGE_SYMBOLS and not is_end:
        column = max(column - 1, 0)

    return utf8_offset_to_codepoint(line, column)


def message_column_to_utf16(line: str, column: int, symbol: str, *, is_end: bool = False) -> int:
    """Convert a checker-specific message column to a UTF-16 code-unit offset."""
    codepoint_offset = message_column_to_codepoint(line, column, symbol, is_end=is_end)
    return codepoint_offset_to_utf16(line, codepoint_offset)
