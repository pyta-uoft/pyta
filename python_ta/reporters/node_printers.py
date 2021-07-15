"""Specify how errors should be rendered."""
import astroid
from enum import Enum


def render_message(msg, node, source_lines):
    """Render a message based on type."""
    renderer = CUSTOM_MESSAGES.get(msg.symbol, render_generic)
    yield from renderer(msg, node, source_lines)


def render_generic(msg, node=None, source_lines=None):
    """Default rendering for a message."""
    if node is not None:
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


def render_missing_docstring(_msg, node, source_lines=None):
    """Render a missing docstring message."""
    if isinstance(node, astroid.Module):
        yield (None, slice(None, None), LineType.DOCSTRING, '"""YOUR DOCSTRING HERE"""')
        yield from render_context(1, 3, source_lines)
    elif isinstance(node, astroid.ClassDef) or isinstance(node, astroid.FunctionDef):
        start = node.fromlineno
        end = node.body[0].fromlineno
        yield from render_context(start, end, source_lines)
        # Calculate indentation
        body = source_lines[end-1]
        indentation = len(body) - len(body.lstrip())
        yield (None, slice(None, None), LineType.DOCSTRING,
               body[:indentation] + '"""YOUR DOCSTRING HERE"""')
        yield from render_context(end, end + 2, source_lines)


def render_trailing_newlines(msg, _node, source_lines=None):
    """Render a trailing newlines message."""
    start_line = msg.line - 1
    yield from render_context(start_line - 2, start_line, source_lines)
    yield from ((line, slice(None, None), LineType.OTHER, source_lines[line-1])
                for line in range(start_line, len(source_lines) + 1))


def render_context(start, stop, source_lines):
    """Helper for rendering context lines."""
    start, stop = max(start, 1), min(stop, len(source_lines))
    yield from ((line, slice(None, None), LineType.CONTEXT, source_lines[line-1])
                for line in range(start, stop))


def render_missing_return_type(_msg, node, source_lines=None):
    """Render a type annotation return message."""
    start_line, start_col = node.fromlineno, node.parent.col_offset
    end_line, end_col = node.end_lineno, node.end_col_offset

    # Display up to 2 lines before node for context:
    yield from render_context(start_line - 2, start_line, source_lines)
    yield from ((line, slice(None, end_col + 1), LineType.ERROR, source_lines[line-1]) for line in
                range(start_line, end_line + 1))
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


CUSTOM_MESSAGES = {
    'missing-module-docstring': render_missing_docstring,
    'missing-class-docstring': render_missing_docstring,
    'missing-function-docstring': render_missing_docstring,
    'trailing-newlines': render_trailing_newlines,
    'missing-return-type': render_missing_return_type,
    'too-many-arguments': render_too_many_arguments,
    'missing-space-in-doctest': render_missing_space_in_doctest
}


class LineType(Enum):
    """An enumeration for _add_line method line types."""
    ERROR = 1       # line with error
    CONTEXT = 2     # non-error/other line added for context
    OTHER = 3       # line included in source but not error
    ELLIPSIS = 5    # code replaced with ellipsis
    DOCSTRING = 6   # docstring needed warning
