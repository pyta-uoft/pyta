"""Specify how errors should be rendered."""
import astroid
from enum import Enum


def render_message(msg, source_lines):
    """Render a message based on type."""
    renderer = CUSTOM_MESSAGES.get(msg.symbol, render_generic)
    yield from renderer(msg, source_lines)


def render_generic(msg, source_lines=None):
    """Default rendering for a message."""
    if hasattr(msg, 'node') and msg.node is not None:
        node = msg.node
        start_line, start_col = node.fromlineno, node.col_offset
        end_line, end_col = node.end_lineno, node.end_col_offset

        # Display up to 2 lines before node for context:
        yield from render_context(start_line - 2, start_line, source_lines)

        if start_line == end_line:
            yield (start_line, slice(start_col, end_col), LineType.ERROR, source_lines[start_line-1])
        else:
            yield (start_line, slice(start_col, None), LineType.ERROR, source_lines[start_line-1])
            yield from ((line, slice(None, None), LineType.ERROR, source_lines[line-1]) for line in range(start_line+1, end_line))
            yield (end_line, slice(None, end_col), LineType.ERROR, source_lines[end_line-1])

        # Display up to 2 lines after node for context:
        yield from render_context(end_line + 1, end_line + 3, source_lines)

    else:
        line = msg.line
        yield from render_context(line - 2, line, source_lines)
        yield (line, slice(None, None), LineType.ERROR, source_lines[line - 1])
        yield from render_context(line + 1, line + 3, source_lines)


def render_missing_docstring(msg, source_lines=None):
    """Render a missing docstring message"""
    if isinstance(msg.node, astroid.Module):
        yield (None, slice(None, None), LineType.DOCSTRING, '"""YOUR DOCSTRING HERE"""')
        yield from render_context(1, 3, source_lines)
    elif isinstance(msg.node, astroid.ClassDef) or isinstance(msg.node, astroid.FunctionDef):
        start = msg.node.fromlineno
        if isinstance(msg.node, astroid.ClassDef):
            end = msg.node.body[0].fromlineno
        else:
            end = msg.node.args.end_lineno + 1
        yield from render_context(start, end, source_lines)
        # Calculate indentation
        body = source_lines[end-1]
        indentation = len(body) - len(body.lstrip())
        yield (None, slice(None, None), LineType.DOCSTRING,
               body[:indentation] + '"""YOUR DOCSTRING HERE"""')
        yield from render_context(end, end + 2, source_lines)


def render_trailing_newlines(msg, source_lines=None):
    start_line = msg.line - 1
    yield from render_context(start_line - 2, start_line, source_lines)
    yield from ((line, slice(None, None), LineType.OTHER, source_lines[line-1])
                for line in range(start_line, len(source_lines) + 1))


def render_context(start, stop, source_lines):
    """Helper for rendering context lines."""
    start, stop = max(start, 1), min(stop, len(source_lines))
    yield from ((line, slice(None, None), LineType.CONTEXT, source_lines[line-1])
                for line in range(start, stop))


def render_bad_whitespace(msg, source_lines=None):
    """Extract column information from caret position within message string"""
    start, stop = None, None
    last_line = msg.msg.split('\n')[-1]
    if '^' in last_line:
        start = last_line.index('^')
        stop = start + 1

    line = msg.line
    yield from render_context(line - 2, line, source_lines)
    yield (line, slice(start, stop), LineType.ERROR, source_lines[line - 1])
    yield from render_context(line + 1, line + 3, source_lines)


CUSTOM_MESSAGES = {
    'missing-docstring': render_missing_docstring,
    'trailing-newlines': render_trailing_newlines,
    'bad-whitespace': render_bad_whitespace,
}


class LineType(Enum):
    """An enumeration for _add_line method line types."""
    ERROR = 1       # line with error
    CONTEXT = 2     # non-error/other line added for context
    OTHER = 3       # line included in source but not error
    ELLIPSIS = 5    # code replaced with ellipsis
    DOCSTRING = 6   # docstring needed warning
