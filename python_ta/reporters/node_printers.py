"""Specify how errors should be rendered."""
import re
from enum import Enum

from astroid import nodes

NEW_BLANK_LINE_MESSAGE = "# INSERT NEW BLANK LINE HERE"


def render_message(msg, node, source_lines):
    """Render a message based on type."""
    renderer = CUSTOM_MESSAGES.get(msg.symbol, render_generic)
    yield from renderer(msg, node, source_lines)


def render_generic(msg, node=None, source_lines=None):
    """Default rendering for a message."""
    if node is not None:
        start_line, start_col = node.fromlineno, node.col_offset

        if isinstance(node, (nodes.FunctionDef, nodes.ClassDef)):
            end_line, end_col = start_line, None
        else:
            end_line, end_col = node.end_lineno, node.end_col_offset

        # Display up to 2 lines before node for context:
        yield from render_context(start_line - 2, start_line, source_lines)

        if start_line == end_line:
            yield (
                start_line,
                slice(start_col, end_col),
                LineType.ERROR,
                source_lines[start_line - 1],
            )
        else:
            yield (start_line, slice(start_col, None), LineType.ERROR, source_lines[start_line - 1])
            yield from (
                (line, slice(None, None), LineType.ERROR, source_lines[line - 1])
                for line in range(start_line + 1, end_line)
            )
            yield (end_line, slice(None, end_col), LineType.ERROR, source_lines[end_line - 1])

        # Display up to 2 lines after node for context:
        yield from render_context(end_line + 1, end_line + 3, source_lines)

    else:
        line = msg.line
        yield from render_context(line - 2, line, source_lines)
        yield (line, slice(None, None), LineType.ERROR, source_lines[line - 1])
        yield from render_context(line + 1, line + 3, source_lines)


def render_missing_docstring(_msg, node, source_lines=None):
    """Render a missing docstring message."""
    if isinstance(node, nodes.Module):
        yield (None, slice(None, None), LineType.DOCSTRING, '"""YOUR DOCSTRING HERE"""')
        yield from render_context(1, 3, source_lines)
    elif isinstance(node, nodes.ClassDef) or isinstance(node, nodes.FunctionDef):
        start = node.fromlineno
        end = node.body[0].fromlineno
        yield from render_context(start, end, source_lines)
        # Calculate indentation
        body = source_lines[end - 1]
        indentation = len(body) - len(body.lstrip())
        yield (
            None,
            slice(None, None),
            LineType.DOCSTRING,
            body[:indentation] + '"""YOUR DOCSTRING HERE"""',
        )
        yield from render_context(end, end + 2, source_lines)


def render_trailing_newlines(msg, _node, source_lines=None):
    """Render a trailing newlines message."""
    start_line = msg.line - 1
    yield from render_context(start_line - 2, start_line, source_lines)
    yield from (
        (line, slice(None, None), LineType.OTHER, source_lines[line - 1])
        for line in range(start_line, len(source_lines) + 1)
    )


def render_trailing_whitespace(msg, _node, source_lines=None):
    """Render a trailing whitespace message."""
    line = msg.line
    start_index, end_index = len(source_lines[line - 1].rstrip()), len(source_lines[line - 1])
    yield from render_context(line - 1, line, source_lines)
    yield (line, slice(start_index, end_index), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 2, source_lines)


def render_context(start, stop, source_lines):
    """Helper for rendering context lines."""
    start, stop = max(start, 1), min(stop, len(source_lines))
    yield from (
        (line, slice(None, None), LineType.CONTEXT, source_lines[line - 1])
        for line in range(start, stop)
    )


def render_missing_return_type(_msg, node, source_lines=None):
    """Render a type annotation return message."""
    start_line, start_col = node.fromlineno, node.parent.col_offset
    end_line, end_col = node.end_lineno, node.end_col_offset

    # Display up to 2 lines before node for context:
    yield from render_context(start_line - 2, start_line, source_lines)
    yield from (
        (line, slice(None, end_col + 1), LineType.ERROR, source_lines[line - 1])
        for line in range(start_line, end_line + 1)
    )
    # Display up to 2 lines after node for context:
    yield from render_context(end_line + 1, end_line + 3, source_lines)


def render_too_many_arguments(msg, node, source_lines=None):
    """Render a too many arguments message."""
    # node is a FunctionDef node so replace it with its Arguments child
    yield from render_generic(msg, node.args, source_lines)


def render_missing_space_in_doctest(msg, _node, source_lines=None):
    """Render a missing space in doctest message"""
    line = msg.line

    # Display 2 lines before and after the erroneous line
    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(None, None), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors(msg, _node, source_lines=None):
    """Render a PEP8 error message."""
    if "indentation contains mixed spaces and tabs" in msg.msg:
        yield from render_pep8_errors_e101(msg, _node, source_lines)
    elif "expected an indented block (comment)" in msg.msg:
        yield from render_pep8_errors_e115(msg, _node, source_lines)
    elif "unexpected indentation (comment)" in msg.msg:
        yield from render_pep8_errors_e116(msg, _node, source_lines)
    elif (
        "continuation line missing indentation or outdented" in msg.msg
        or "continuation line over-indented for visual indent" in msg.msg
        or "continuation line unaligned for hanging indent" in msg.msg
    ):
        yield from render_pep8_errors_e122_and_e127_and_e131(msg, _node, source_lines)
    elif "closing bracket does not match visual indentation" in msg.msg:
        yield from render_pep8_errors_e124(msg, _node, source_lines)
    elif (
        "continuation line with same indent as next logical line" in msg.msg
        or "visually indented line with same indent as next logical line" in msg.msg
    ):
        yield from render_pep8_errors_e125_and_e129(msg, _node, source_lines)
    elif "continuation line under-indented for visual indent" in msg.msg:
        yield from render_pep8_errors_e128(msg, _node, source_lines)
    elif "whitespace after '('" in msg.msg:
        yield from render_pep8_errors_e201(msg, _node, source_lines)
    elif "whitespace before ')'" in msg.msg:
        yield from render_pep8_errors_e202(msg, _node, source_lines)
    elif "whitespace before '('" in msg.msg:
        yield from render_pep8_errors_e211(msg, _node, source_lines)
    elif "multiple spaces before operator" in msg.msg:
        yield from render_pep8_errors_e221(msg, _node, source_lines)
    elif "tab before operator" in msg.msg:
        yield from render_pep8_errors_e223(msg, _node, source_lines)
    elif "tab after operator" in msg.msg or "tab after keyword" in msg.msg:
        yield from render_pep8_errors_e224_and_e273(msg, _node, source_lines)
    elif "missing whitespace around bitwise or shift operator" in msg.msg:
        yield from render_pep8_errors_e227(msg, _node, source_lines)
    elif "missing whitespace around modulo operator" in msg.msg:
        yield from render_pep8_errors_e228(msg, _node, source_lines)
    elif "unexpected spaces around keyword / parameter equals" in msg.msg:
        yield from render_pep8_errors_e251(msg, _node, source_lines)
    elif "at least two spaces before inline comment" in msg.msg:
        yield from render_pep8_errors_e261(msg, _node, source_lines)
    elif "block comment should start with '# '" in msg.msg:
        yield from render_pep8_errors_e265(msg, _node, source_lines)
    elif "too many leading '#' for block comment" in msg.msg:
        yield from render_pep8_errors_e266(msg, _node, source_lines)
    elif "multiple spaces before keyword" in msg.msg:
        yield from render_pep8_errors_e272(msg, _node, source_lines)
    elif "missing whitespace after keyword" in msg.msg:
        yield from render_pep8_errors_e275(msg, _node, source_lines)
    elif "expected 1 blank line," in msg.msg:
        yield from render_pep8_errors_e301(msg, _node, source_lines)
    elif "expected 2 blank lines," in msg.msg:
        yield from render_pep8_errors_e302(msg, _node, source_lines)
    elif "too many blank lines" in msg.msg:
        yield from render_pep8_errors_e303(msg, _node, source_lines)
    elif "blank lines found after function decorator" in msg.msg:
        yield from render_pep8_errors_e304(msg, _node, source_lines)
    elif "expected 2 blank lines after class or function definition" in msg.msg:
        yield from render_pep8_errors_e305(msg, _node, source_lines)
    elif "expected 1 blank line before a nested definition" in msg.msg:
        yield from render_pep8_errors_e306(msg, _node, source_lines)
    else:
        yield from render_generic(msg, _node, source_lines)


def render_blank_line(line):
    """Render a blank line for a PEP8 error message."""
    yield (line + 1, slice(None, None), LineType.ERROR, " " * 28)


def render_pep8_errors_e101(msg, _node, source_lines=None):
    """Render a PEP8 indentation contains mixed spaces and tabs message."""
    line = msg.line
    curr_idx = len(source_lines[line - 1]) - len(source_lines[line - 1].lstrip())
    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(0, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e115(msg, _node, source_lines=None):
    """Render a PEP8 expected an indented block (comment) message."""
    line = msg.line

    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(0, len(source_lines[line - 1])),
        LineType.ERROR,
        source_lines[line - 1] + "  # INDENT THIS LINE",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e116(msg, _node, source_lines=None):
    """Render a PEP8 unexpected indentation (comment) message"""
    line = msg.line
    curr_idx = len(source_lines[line - 1]) - len(source_lines[line - 1].lstrip())
    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(0, curr_idx),
        LineType.ERROR,
        source_lines[line - 1],
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e122_and_e127_and_e131(msg, _node, source_lines=None):
    """
    Render a PEP8 continuation line missing indentation or outdented message, a line over-indented for visual indent
    message, and a continuation line unaligned for hanging indent message.
    """
    line = msg.line
    curr_line_start_index = len(source_lines[line - 1]) - len(source_lines[line - 1].lstrip())
    end_index = curr_line_start_index if curr_line_start_index > 0 else len(source_lines[line - 1])
    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(0, end_index),
        LineType.ERROR,
        source_lines[line - 1],
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e124(msg, _node, source_lines=None):
    """Render a PEP8 closing bracket does not match visual indentation message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, col + 1), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e125_and_e129(msg, _node, source_lines=None):
    """Render a PEP8 continuation line with same indent as next logical line message
    AND a PEP8 visually indented line with same indent as next logical line messsage"""
    line = msg.line
    curr_idx = len(source_lines[line - 1]) - len(source_lines[line - 1].lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(curr_idx, len(source_lines[line - 1])),
        LineType.ERROR,
        source_lines[line - 1] + " " * 2 + "# INDENT THIS LINE",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e128(msg, _node, source_lines):
    """Render a PEP8 continuation line under-indented for visual indent message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(0, col if col != 0 else None), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e201(msg, _node, source_lines=None):
    """Render a PEP8 whitespace after '(' message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e202(msg, _node, source_lines=None):
    """Render a PEP8 whitespace before ')' message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e211(msg, _node, source_lines=None):
    """Render a PEP8 whitespace before '(' message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e221(msg, _node, source_lines=None):
    """Render a PEP8 multiple spaces before operator message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e223(msg, _node, source_lines=None):
    """Render a PEP8 tab before operator message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = (
        col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip("\t"))
    )

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e224_and_e273(msg, _node, source_lines):
    """Render a PEP8 tab after operator message and a PEP8 tab after keyword message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = (
        col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip("\t"))
    )

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e227(msg, _node, source_lines=None):
    """Render a PEP8 missing whitespace around bitwise or shift operator message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    # Check which operator to get the correct range of the line to highlight.
    # Default highlight is one character, but may be updated to two.
    # Note that only binary bitwise operators that are more than one character are included.
    operators = {">>", "<<"}
    end_idx = col + 1
    end_idx = end_idx + 1 if source_lines[line - 1][col : col + 2] in operators else end_idx

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, end_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e228(msg, _node, source_lines=None):
    """Render a PEP8 missing whitespace around modulo operator message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])

    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(col, col + 1),
        LineType.ERROR,
        source_lines[line - 1] + "  # INSERT A SPACE BEFORE AND AFTER THE % OPERATOR",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e251(msg, _node, source_lines=None):
    """Render a PEP8 unexpected spaces around keyword / parameter equals message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    equals_sign_idx = source_lines[line - 1][col:].find("=")
    code = source_lines[line - 1][col : col + equals_sign_idx if equals_sign_idx != -1 else None]
    end_idx = col + len(code) - len(code.lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, end_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e261(msg, _node, source_lines=None):
    """Render a PEP8 at least two spaces before inline comment message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])

    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(col, len(source_lines[line - 1])),
        LineType.ERROR,
        source_lines[line - 1] + "  # INSERT TWO SPACES BEFORE THE '#'",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e265(msg, _node, source_lines=None):
    """Render a PEP8 block comment should start with '# ' message."""
    line = msg.line
    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(0, len(source_lines[line - 1])),
        LineType.ERROR,
        source_lines[line - 1] + "  # INSERT SPACE AFTER THE '#'",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e266(msg, _node, source_lines=None):
    """Render a PEP8 too many leading ‘#’ for block comment message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = (
        col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip("#"))
    )

    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(col, curr_idx),
        LineType.ERROR,
        source_lines[line - 1] + "  # THERE SHOULD ONLY BE ONE '#'",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e272(msg, _node, source_lines=None):
    """Render a PEP8 multiple spaces before keyword message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])
    curr_idx = col + len(source_lines[line - 1][col:]) - len(source_lines[line - 1][col:].lstrip())

    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(col, curr_idx), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e275(msg, _node, source_lines=None):
    """Render a PEP8 missing whitespace after keyword message."""
    line = msg.line
    res = re.search(r"column (\d+)", msg.msg)
    col = int(res.group().split()[-1])

    # Get the range for highlighting the corresponding keyword.
    keyword = source_lines[line - 1][:col].split()[-1]
    keyword_idx = source_lines[line - 1].index(keyword)

    yield from render_context(line - 2, line, source_lines)
    yield (
        line,
        slice(keyword_idx, col),
        LineType.ERROR,
        source_lines[line - 1] + "  # INSERT SPACE AFTER KEYWORD",
    )
    yield from render_context(line + 1, line + 3, source_lines)


def render_pep8_errors_e301(msg, _node, source_lines=None):
    """Render a PEP8 expected 1 blank line message."""
    line = msg.line - 1
    yield from render_context(line - 1, line + 1, source_lines)
    body = source_lines[line]
    indentation = len(body) - len(body.lstrip())
    yield (
        None,
        slice(None, None),
        LineType.ERROR,
        body[:indentation] + NEW_BLANK_LINE_MESSAGE + " " * indentation,
    )
    yield from render_context(msg.line, msg.line + 2, source_lines)


def render_pep8_errors_e302(msg, _node, source_lines=None):
    """Render a PEP8 expected 2 blank lines message."""
    line = msg.line - 1
    if "found 0" in msg.msg:
        yield from render_context(line - 1, line + 1, source_lines)
        yield from (
            (
                None,
                slice(None, None),
                LineType.ERROR,
                NEW_BLANK_LINE_MESSAGE,
            )
            for _ in range(0, 2)
        )
    else:
        line -= 1
        yield from render_context(line - 1, line + 1, source_lines)
        yield from render_blank_line(line)
        yield (None, slice(None, None), LineType.ERROR, NEW_BLANK_LINE_MESSAGE)
    yield from render_context(msg.line, msg.line + 2, source_lines)


def render_pep8_errors_e303(msg, _node, source_lines=None):
    """Render a PEP8 too many blank lines message."""
    line = msg.line - 1
    while source_lines[line - 1].strip() == "":
        line -= 1
    yield from render_context(line - 1, line + 1, source_lines)
    body = source_lines[msg.line - 1]
    indentation = len(body) - len(body.lstrip())
    yield from (
        (curr_line, slice(None, None), LineType.ERROR, " " * (indentation + 28))
        for curr_line in range(line + 1, msg.line)
    )
    yield from render_context(msg.line, msg.line + 2, source_lines)


def render_pep8_errors_e304(msg, _node, source_lines=None):
    """Render a PEP8 blank lines found after function decorator message."""
    line = msg.line - 1
    while source_lines[line - 1].strip() == "":
        line -= 1
    yield from render_context(line - 1, line + 1, source_lines)
    yield from (
        (curr_line, slice(None, None), LineType.ERROR, " " * 28)
        for curr_line in range(line + 1, msg.line)
    )
    yield from render_context(msg.line, msg.line + 2, source_lines)


def render_pep8_errors_e305(msg, _node, source_lines=None):
    """Render a PEP8 expected 2 blank lines after class or function definition message."""
    line = msg.line - 1
    if "found 0" in msg.msg:
        yield from render_context(line - 1, line + 1, source_lines)
        yield from (
            (
                None,
                slice(None, None),
                LineType.ERROR,
                NEW_BLANK_LINE_MESSAGE,
            )
            for _ in range(0, 2)
        )
    else:
        line -= 1
        yield from render_context(line - 1, line + 1, source_lines)
        yield from render_blank_line(line)
        yield (None, slice(None, None), LineType.ERROR, NEW_BLANK_LINE_MESSAGE)
    yield from render_context(msg.line, msg.line + 2, source_lines)


def render_pep8_errors_e306(msg, _node, source_lines=None):
    """Render a PEP8 expected 1 blank line before a nested definition message."""
    line = msg.line - 1
    yield from render_context(line - 1, line + 1, source_lines)
    body = source_lines[line]
    indentation = len(body) - len(body.lstrip())
    yield (
        None,
        slice(None, None),
        LineType.ERROR,
        body[:indentation] + NEW_BLANK_LINE_MESSAGE + " " * indentation,
    )
    yield from render_context(msg.line, msg.line + 2, source_lines)


CUSTOM_MESSAGES = {
    "missing-module-docstring": render_missing_docstring,
    "missing-class-docstring": render_missing_docstring,
    "missing-function-docstring": render_missing_docstring,
    "trailing-newlines": render_trailing_newlines,
    "trailing-whitespace": render_trailing_whitespace,
    "missing-return-type": render_missing_return_type,
    "too-many-arguments": render_too_many_arguments,
    "missing-space-in-doctest": render_missing_space_in_doctest,
    "pep8-errors": render_pep8_errors,
}


class LineType(Enum):
    """An enumeration for _add_line method line types."""

    ERROR = 1  # line with error
    CONTEXT = 2  # non-error/other line added for context
    OTHER = 3  # line included in source but not error
    ELLIPSIS = 5  # code replaced with ellipsis
    DOCSTRING = 6  # docstring needed warning
