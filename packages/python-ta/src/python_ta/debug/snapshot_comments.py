"""
Run a Python file in which "magic comments" of the form `# pyta: snapshot(...)` are turned into
calls to python_ta.debug.snapshot.snapshot, so that memory snapshots can be taken without
importing or calling snapshot directly.

The comments are found with `tokenize` (since the `ast` module discards comments). The file is parsed
with `ast`, a call node is inserted at each comment, and the modified tree is compiled and run.
"""

from __future__ import annotations

import ast
import difflib
import inspect
import io
import os
import re
import sys
import tokenize
import types
from dataclasses import dataclass

from .snapshot import snapshot

# The name the inserted calls use for snapshot. The leading "__" keeps it out of the global
# variables captured by snapshot, and the trailing "__" prevents name mangling in class bodies.
_SNAPSHOT_ALIAS = "__pyta_snapshot__"

MAGIC_COMMENT_PATTERN = re.compile(r"#\s*pyta:")

_NON_CODE_TOKENS = {
    tokenize.COMMENT,
    tokenize.NL,
    tokenize.NEWLINE,
    tokenize.INDENT,
    tokenize.DEDENT,
    tokenize.ENDMARKER,
}

# Statements that a call inserted directly after could never be reached
_UNREACHABLE_AFTER = (ast.Return, ast.Raise, ast.Break, ast.Continue)


@dataclass
class MagicComment:
    """A `# pyta: ...` comment found in source code.

    Instance attributes:
        lineno: the line the comment is on
        comment_col: the column of the comment's "#"
        call_col: the column where the call text starts
        call_text: the text after "pyta:", e.g. "snapshot(save=True)"
        line: the full source line containing the comment
        standalone: whether the comment is the only thing on its line
    """

    lineno: int
    comment_col: int
    call_col: int
    call_text: str
    line: str
    standalone: bool = True


def run_with_snapshot_comments(path: str) -> None:
    """Run the Python file at `path`, replacing each `# pyta: snapshot(...)` comment with a call to
    python_ta.debug.snapshot.snapshot.

    The file runs as the "__main__" module, as it would with `python <path>`. Each snapshot call
    runs whenever execution reaches the line of its comment. Unless the comment passes `save`
    itself, `save=True` is used, so that a MemoryViz diagram is produced.

    A comment on its own line takes a snapshot between the statements around it. A comment at the
    end of a line of code takes a snapshot after that line runs.

    Raises a SyntaxError (before any of the file runs) if a magic comment is not a valid call to
    snapshot, or if it is not clear where in the code the comment belongs.
    """
    path = os.path.abspath(os.path.expanduser(path))
    with tokenize.open(path) as f:
        source = f.read()
    code = compile(_add_snapshot_calls(source, path), path, "exec")

    # Make fake __main__ module to run the code in, so that it sees the file as "__main__" and can import
    module = types.ModuleType("__main__")
    module.__file__ = path

    # Save the current interpreter state
    original_main = sys.modules.get("__main__")
    original_argv = sys.argv
    original_path = sys.path[:]

    # Make it look like the file is being run as a script
    sys.modules["__main__"] = module
    sys.argv = [path]
    sys.path.insert(0, os.path.dirname(path))
    try:
        exec(code, module.__dict__)
    finally:
        # Restore the interpreter state
        if original_main is None:
            sys.modules.pop("__main__", None)
        else:
            sys.modules["__main__"] = original_main
        sys.argv = original_argv
        sys.path[:] = original_path


def _add_snapshot_calls(source: str, filename: str = "<unknown>") -> ast.Module:
    """Return the ast of `source` with a snapshot call inserted for each `# pyta: snapshot(...)`
    comment, along with an import of snapshot function.

    The original statements keep their line numbers, and each inserted call is given the line
    number of its comment.
    """
    tree = ast.parse(source, filename)
    comments, code_lines = _find_magic_comments(source)
    if not comments:
        return tree

    statements = _statements_with_blocks(tree)
    for comment in comments:
        call = _parse_snapshot_call(comment, filename)

        # Find the block of statements that the call should be inserted into, and insert it in order
        block = _find_block(comment, statements, code_lines, filename)
        block.append(call)
        block.sort(key=lambda stmt: stmt.lineno)

    import_node = ast.ImportFrom(
        module="python_ta.debug.snapshot",
        names=[ast.alias(name="snapshot", asname=_SNAPSHOT_ALIAS)],
        level=0,
        lineno=1,
        col_offset=0,
    )
    tree.body.insert(_import_index(tree.body), import_node)

    # Fill in missing location details for the new nodes
    return ast.fix_missing_locations(tree)


def _find_magic_comments(source: str) -> tuple[list[MagicComment], set[int]]:
    """Return the magic comments in the source code, and the set of line numbers that contain code."""
    comments = []
    code_lines: set[int] = set()

    for tok in tokenize.generate_tokens(io.StringIO(source).readline):
        if tok.type == tokenize.COMMENT:
            match = MAGIC_COMMENT_PATTERN.match(tok.string)
            if match is None:
                continue
            rest = tok.string[match.end() :]
            call_text = rest.strip()
            lineno, comment_col = tok.start
            call_col = comment_col + match.end() + (len(rest) - len(rest.lstrip()))
            comments.append(MagicComment(lineno, comment_col, call_col, call_text, tok.line))
        elif tok.type not in _NON_CODE_TOKENS:
            code_lines.update(range(tok.start[0], tok.end[0] + 1))

    # Determine if magic comments are on their own lines or at the end of a line of code
    for comment in comments:
        comment.standalone = comment.lineno not in code_lines
    return comments, code_lines


def _parse_snapshot_call(comment: MagicComment, filename: str) -> ast.Expr:
    """Return a statement calling snapshot, parsed from the text of `comment`.

    The statement is positioned at the comment, and calls snapshot under the name _SNAPSHOT_ALIAS.
    """
    try:
        call = ast.parse(comment.call_text, mode="eval").body
    except SyntaxError as e:
        raise _comment_error(f"invalid pyta comment: {e.msg}", comment, filename) from None

    # Check that the comment is a call to snapshot, and that it has valid arguments
    if not (
        isinstance(call, ast.Call)
        and isinstance(call.func, ast.Name)
        and call.func.id == "snapshot"
    ):
        raise _comment_error(
            "a pyta comment must be a call to snapshot, e.g. '# pyta: snapshot()'",
            comment,
            filename,
        )

    parameters = inspect.signature(snapshot).parameters
    if len(call.args) > len(parameters):
        raise _comment_error(
            f"snapshot() takes at most {len(parameters)} positional arguments", comment, filename
        )
    for keyword in call.keywords:
        if keyword.arg is not None and keyword.arg not in parameters:
            message = f"snapshot() got an unexpected keyword argument '{keyword.arg}'"
            suggestions = difflib.get_close_matches(keyword.arg, parameters, n=1)
            if suggestions:
                message += f". Did you mean '{suggestions[0]}'?"
            raise _comment_error(message, comment, filename)

    # The value returned by the inserted call is discarded, so save the snapshot by default
    if not call.args and all(keyword.arg not in ("save", None) for keyword in call.keywords):
        call.keywords.insert(0, ast.keyword(arg="save", value=ast.Constant(value=True)))

    call.func.id = _SNAPSHOT_ALIAS
    stmt = ast.fix_missing_locations(ast.copy_location(ast.Expr(value=call), call))

    # Move the statement from the start of the call text to the comment's position
    ast.increment_lineno(stmt, comment.lineno - 1)
    for node in ast.walk(stmt):
        for attribute in ("col_offset", "end_col_offset"):
            offset = getattr(node, attribute, None)
            if offset is not None:
                setattr(node, attribute, offset + comment.call_col)
    return stmt


def _find_block(
    comment: MagicComment,
    statements: list[tuple[ast.stmt, list[ast.stmt]]],
    code_lines: set[int],
    filename: str,
) -> list[ast.stmt]:
    """Return the list of statements that the call for `comment` should be inserted into."""

    # If comment is not on its own line, it must be at the end of a statement, and the call should be inserted after that statement
    if not comment.standalone:
        # Use the innermost statement that ends on the comment's line
        on_line = [
            (stmt, block) for stmt, block in statements if _end_lineno(stmt) == comment.lineno
        ]
        if not on_line:
            raise _comment_error(
                "this pyta comment must be on its own line, or at the end of a statement",
                comment,
                filename,
            )
        target, block = max(on_line, key=lambda pair: (pair[0].lineno, pair[0].col_offset))
        if isinstance(target, _UNREACHABLE_AFTER):
            raise _comment_error(
                f"a snapshot after this '{type(target).__name__.lower()}' statement would never "
                "run; put the pyta comment on its own line before it",
                comment,
                filename,
            )
        return block

    # If comment is on its own line, find the statement before or after it at the same indentation
    aligned = [
        (stmt, block) for stmt, block in statements if stmt.col_offset == comment.comment_col
    ]

    # The statement directly before the comment, at the same indentation
    before = [(stmt, block) for stmt, block in aligned if _end_lineno(stmt) < comment.lineno]
    if before:
        prev, block = max(before, key=lambda pair: _end_lineno(pair[0]))
        if not _has_code_between(code_lines, _end_lineno(prev), comment.lineno):
            return block

    # The statement directly after the comment, at the same indentation
    after = [(stmt, block) for stmt, block in aligned if _start_lineno(stmt) > comment.lineno]
    if after:
        nxt, block = min(after, key=lambda pair: _start_lineno(pair[0]))
        if not _has_code_between(code_lines, comment.lineno, _start_lineno(nxt)):
            return block

    raise _comment_error(
        "could not tell where this pyta comment belongs; "
        "indent it to line up with the statements around it",
        comment,
        filename,
    )


def _statements_with_blocks(tree: ast.Module) -> list[tuple[ast.stmt, list[ast.stmt]]]:
    """Return every statement in `tree`, paired with the list of statements that contains it."""
    statements: list[tuple[ast.stmt, list[ast.stmt]]] = []
    for node in ast.walk(tree):
        for field in ("body", "orelse", "finalbody"):
            block = getattr(node, field, None)
            if isinstance(block, list):
                statements.extend((stmt, block) for stmt in block if isinstance(stmt, ast.stmt))
    return statements


def _start_lineno(stmt: ast.stmt) -> int:
    """Return the first line of `stmt`, including any decorators."""
    decorators = getattr(stmt, "decorator_list", [])
    return min([stmt.lineno] + [decorator.lineno for decorator in decorators])


def _end_lineno(stmt: ast.stmt) -> int:
    """Return the last line of `stmt`."""
    return stmt.end_lineno if stmt.end_lineno is not None else stmt.lineno


def _has_code_between(code_lines: set[int], start: int, end: int) -> bool:
    """Return whether any line strictly between `start` and `end` contains code."""
    return any(start < lineno < end for lineno in code_lines)


def _import_index(body: list[ast.stmt]) -> int:
    """Return the index in a module body after its docstring and any `from __future__` imports."""
    index = 0
    if (
        body
        and isinstance(body[0], ast.Expr)
        and isinstance(body[0].value, ast.Constant)
        and isinstance(body[0].value.value, str)
    ):
        index = 1
    while index < len(body):
        stmt = body[index]
        if not (isinstance(stmt, ast.ImportFrom) and stmt.module == "__future__"):
            break
        index += 1
    return index


def _comment_error(message: str, comment: MagicComment, filename: str) -> SyntaxError:
    """Return a SyntaxError pointing at the call text of `comment`."""
    return SyntaxError(message, (filename, comment.lineno, comment.call_col + 1, comment.line))
