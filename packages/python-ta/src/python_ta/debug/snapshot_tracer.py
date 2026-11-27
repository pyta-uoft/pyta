from __future__ import annotations

import ast
import base64
import copy
import inspect
import logging
import os
import re
import socket
import sys
import tokenize
import warnings
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable, Optional

import asttokens
from asttokens.util import Token
from jinja2 import Environment, FileSystemLoader

from ..util.servers.one_shot_server import open_html_in_browser
from .id_tracker import IDTracker
from .snapshot import snapshot, snapshot_to_json
from .util import exec_as_main

if TYPE_CHECKING:
    import types

TRACER_ALIAS = "__snapshot_tracer__"

TRACER_COMMENT_PATTERN = re.compile(r"#\s*pyta:\s*snapshot-tracer-(start|end)\s*")

# Tokens that are not code, skipped when finding the code between the snapshot-tracer comments
_NON_CODE_TOKEN_TYPES = (
    tokenize.NL,
    tokenize.NEWLINE,
    tokenize.COMMENT,
    tokenize.INDENT,
    tokenize.DEDENT,
)


class SnapshotTracer:
    """
    A class used for snapshot-based debugging to visualize program memory at each line in the calling function.

    Instance attributes:
        webstepper: Opens the web-based visualizer.
        snapshots: A list of dictionaries that maps the code line number and corresponding MemoryViz JSON snapshot at each traced line.
        _webstepper_options: A dictionary of configuration options for the webstepper visualizer.
        _snapshot_args: A dictionary of keyword arguments to pass to the `snapshot` function.
        _start_lineno: Line number of the first line to be displayed in the code section of the Webstepper.
        _end_lineno: Line number of the last line to be displayed in the code section of the Webstepper.
        _origin_file: The absolute path of the module where SnapshotTracer is used.
        _module_source_lines: A list of strings representing the source code lines of the module where SnapshotTracer is used.
    """

    webstepper: bool
    _webstepper_options: dict[str, Any]
    _snapshots: list[dict[str, Any]]
    _snapshot_args: dict[str, Any]
    _start_lineno: int
    _end_lineno: int
    _origin_file: str | None
    _module_source_lines: list[str] | None

    def __init__(
        self,
        output_directory: Optional[str] = None,
        webstepper: bool = False,
        webstepper_options: Optional[dict[str, Any]] = None,
        **kwargs,
    ) -> None:
        """Initialize a context manager for snapshot-based debugging.

        Args:
            output_directory: This argument is deprecated; previously used for file-based outputs.
            webstepper: Opens a MemoryViz Webstepper webpage to interactively visualize the resulting memory diagrams.
            webstepper_options: A dictionary of configuration options for the Webstepper visualizer when webstepper=True.
                Supported options: line_context, the number of lines of context to show above and below the traced block in the Webstepper view if > 0.
            **kwargs: All other keyword arguments are passed to `python.debug.snapshot`. Refer to the `snapshot` function for more details.
        """
        if sys.version_info < (3, 10, 0):
            logging.warning("You need Python 3.10 or later to use SnapshotTracer.")
        if output_directory is not None:
            warnings.warn("The output_directory argument is deprecated.", DeprecationWarning)
        self._snapshots = []
        self._snapshot_args = kwargs
        self._snapshot_args["memory_viz_args"] = copy.deepcopy(kwargs.get("memory_viz_args", []))
        self._snapshot_args["exclude_frames"] = copy.deepcopy(kwargs.get("exclude_frames", []))
        self._snapshot_args["exclude_frames"].append("_trace_func")
        self._snapshot_args["exclude_frames"].append("_global_trace_func")
        self.id_tracker = IDTracker()

        self.webstepper = webstepper
        self._webstepper_options = webstepper_options if webstepper_options is not None else {}
        if self._webstepper_options and not self.webstepper:
            warnings.warn(
                "webstepper_options have no effect when webstepper=False. Set webstepper=True to use webstepper_options.",
                UserWarning,
            )
        self._start_lineno = sys.maxsize
        self._end_lineno = 0
        self._origin_file = None
        self._module_source_lines = None

    def _global_trace_func(
        self, frame: types.FrameType, event: str, _arg: Any
    ) -> Callable[[types.FrameType, str, Any], None] | None:
        """Global trace function that handles 'call' events to determine which functions to trace into."""
        if event != "call" or self._origin_file is None:
            return None
        # Only trace functions in the same module as the calling function.
        called_file = os.path.normcase(os.path.abspath(frame.f_code.co_filename))
        if called_file == self._origin_file and frame.f_code.co_name not in (
            self._trace_func.__name__,
            self._global_trace_func.__name__,
        ):
            self._start_lineno = min(self._start_lineno, frame.f_code.co_firstlineno)
            self._end_lineno = max(
                self._end_lineno,
                frame.f_code.co_firstlineno + len(inspect.getsourcelines(frame)[0]) - 1,
            )
            # Return self._trace_func to trace into the called function, otherwise return None to skip tracing.
            return self._trace_func
        return None

    def _trace_func(self, frame: types.FrameType, event: str, _arg: Any) -> None:
        """Local trace function set on each frame to take a snapshot of the variables in the functions specified in `self.include`."""
        if event == "line":
            self._end_lineno = max(self._end_lineno, frame.f_lineno)
            snapshot_output = snapshot(
                id_tracker=self.id_tracker,
                **self._snapshot_args,
            )
            json_data = snapshot_to_json(snapshot_output, id_tracker=self.id_tracker)
            self._snapshots.append(
                {
                    "lineNumber": frame.f_lineno,
                    "memoryVizInput": json_data,
                }
            )

    def __enter__(self):
        """Set up the trace function to take snapshots at each line of code."""
        func_frame = inspect.getouterframes(inspect.currentframe())[1].frame
        # Add 1 to account for the line of the with statement. Keep an earlier start line if
        # one was already set (e.g., by run_with_snapshot_tracer).
        self._start_lineno = min(self._start_lineno, func_frame.f_lineno + 1)
        func_frame.f_trace = self._trace_func
        origin_file = func_frame.f_globals.get("__file__")
        self._origin_file = (
            os.path.normcase(os.path.abspath(origin_file)) if origin_file is not None else None
        )
        if self._origin_file is not None:
            self._module_source_lines = (
                Path(self._origin_file).read_text(encoding="utf-8").splitlines()
            )
        sys.settrace(self._global_trace_func)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        """Remove the trace function. If webstepper=True, open a Webstepper webpage."""
        sys.settrace(None)
        func_frame = inspect.getouterframes(inspect.currentframe())[1]
        func_frame.frame.f_trace = None
        if self.webstepper:
            html_content = self._build_self_contained_html(func_frame.frame)
            self._serve_html(html_content)

    def _build_self_contained_html(self, func_frame: types.FrameType) -> bytes:
        """Build a self-contained HTML string with all assets inlined."""
        webstepper_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "webstepper")

        bundle_path = os.path.join(webstepper_dir, "index.bundle.js")
        with open(bundle_path, "r", encoding="utf-8") as f:
            bundle_content = f.read()

        image_replacements: dict[str, str] = {}
        for image_filename in ["99ee5c67fd0c522b4b6a.png", "fd6133fe40f4f90440d6.png"]:
            image_path = os.path.join(webstepper_dir, image_filename)
            with open(image_path, "rb") as f:
                image_data = f.read()
                base64_data = base64.b64encode(image_data).decode("utf-8")
                data_uri = f"data:image/png;base64,{base64_data}"
                image_replacements[image_filename] = data_uri

        for filename, data_uri in image_replacements.items():
            bundle_content = bundle_content.replace(f'a.p+"{filename}"', f'"{data_uri}"')

        template_loader = FileSystemLoader(webstepper_dir)
        template_env = Environment(loader=template_loader)
        template = template_env.get_template("webstepper_template.html.jinja")

        code_text, start_line_number = self._get_code()

        rendered_html = template.render(
            code_text=code_text,
            start_line_number=start_line_number,
            memory_viz_data=self._snapshots,
            bundle_content=bundle_content,
        )

        return rendered_html.encode("utf-8")

    def _serve_html(self, html_content: bytes) -> None:
        """Serve the HTML content using a one-shot server."""
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]

        open_html_in_browser(html_content, port)

    def _get_code(self) -> tuple[str, int]:
        """Retrieve and save the code string to be displayed in Webstepper.
        Return a tuple of the code string and the starting line number.
        """
        if self._module_source_lines is None or self._start_lineno > self._end_lineno:
            return "", 1
        line_context = self._webstepper_options.get("line_context", 0)
        start_index = max(self._start_lineno - 1 - line_context, 0)
        end_index = min(self._end_lineno + line_context, len(self._module_source_lines))
        return "\n".join(self._module_source_lines[start_index:end_index]), start_index + 1

    @property
    def snapshots(self) -> list[dict[str, Any]]:
        """Return the snapshots taken at each line of code."""
        return self._snapshots


def run_with_snapshot_tracer(path: str, **kwargs: Any) -> SnapshotTracer:
    """Run the given Python file with its code traced by a SnapshotTracer.

    If the file contains a "# pyta: snapshot-tracer-start" comment and a
    "# pyta: snapshot-tracer-end" comment, only the statements between them are traced, as if
    they were inside a `with SnapshotTracer(...):` block. Otherwise, the whole file is traced.

    The two comments must each be on a line by themselves, and be in the same block of code.
    Only the first start comment and the first end comment after it are used.

    The Webstepper opens by default (webstepper=True) once the file finishes running.

    Args:
        path: The path to the Python file to run.
        **kwargs: Keyword arguments passed to SnapshotTracer. Refer to SnapshotTracer for more
            details.

    Returns:
        The SnapshotTracer used to trace the file, which holds the snapshots taken.

    Raises:
        SyntaxError: If the snapshot-tracer comments are used incorrectly.
    """
    # utf-8-sig strips the BOM at the start of the file, which ast.parse would reject
    with open(path, encoding="utf-8-sig") as f:
        source = f.read()

    tokens = asttokens.ASTTokens(source, parse=True, filename=path)
    tree = tokens.tree
    assert isinstance(tree, ast.Module)  # parse=True always builds the module tree

    markers = _find_tracer_comments(tokens, path)
    if markers is not None:
        start, end = markers
        with_node = _wrap_marked_block_in_tracer(tokens, start, end, path)
    else:
        with_node = _wrap_module_in_tracer(tree)
    code = compile(tree, filename=path, mode="exec")

    tracer = SnapshotTracer(**{"webstepper": True, **kwargs})
    if with_node is not None:
        tracer._start_lineno = with_node.lineno + 1
        tracer._end_lineno = with_node.end_lineno or 0

    exec_as_main(code, path, {TRACER_ALIAS: tracer})
    return tracer


def _find_tracer_comments(
    tokens: asttokens.ASTTokens, filename: str
) -> Optional[tuple[Token, Token]]:
    """Return the first "# pyta: snapshot-tracer-start" comment token in the file and the
    first "# pyta: snapshot-tracer-end" comment token after it. Any other snapshot-tracer
    comments are ignored.

    Return None if there are no snapshot-tracer comments.

    Raise a SyntaxError pointing at the comment at fault if the start comment has no end
    comment after it, an end comment has no start comment, or either of the two comments
    is not on a line by itself.

    Args:
        tokens: The tokens of the file.
        filename: The path to the file, used in error messages.
    """
    starts: list[Token] = []
    ends: list[Token] = []
    for tok in tokens.tokens:
        if tok.type == tokenize.COMMENT and (match := TRACER_COMMENT_PATTERN.fullmatch(tok.string)):
            (starts if match.group(1) == "start" else ends).append(tok)
    if not starts and not ends:
        return None

    if not starts:
        raise _comment_error(
            ends[0], "snapshot-tracer-end has no matching snapshot-tracer-start", filename
        )
    start = starts[0]
    end = next((tok for tok in ends if tok.index > start.index), None)
    if end is None:
        raise _comment_error(
            start, "snapshot-tracer-start has no matching snapshot-tracer-end", filename
        )

    for tok in (start, end):
        if tok.line[: tok.start[1]].strip():
            raise _comment_error(
                tok, "a snapshot-tracer comment must be on a line by itself", filename
            )
    return start, end


def _wrap_module_in_tracer(tree: ast.Module) -> Optional[ast.With]:
    """Wrap the body of the given module in a `with` block using the tracer named
    TRACER_ALIAS, and return the new `with` node. Mutates the given module.

    A leading module docstring and any `from __future__` imports stay outside the `with`
    block, as they must come first in a module. The wrapped statements keep their original
    line numbers.

    Return None (and leave the module unchanged) if there are no statements to wrap.

    Args:
        tree: The parsed module to wrap.
    """
    body = tree.body
    num_header = _get_num_header_statements(body)
    header, wrapped = body[:num_header], body[num_header:]
    if not wrapped:
        return None

    # Put the `with` statement on the line before the first wrapped statement
    first = wrapped[0]
    first_lineno = min(
        [first.lineno] + [decorator.lineno for decorator in getattr(first, "decorator_list", [])]
    )
    with_node = _build_with_tracer_statement(wrapped, first_lineno - 1, 0)
    tree.body = header + [with_node]
    return with_node


def _get_num_header_statements(body: list[ast.stmt]) -> int:
    """Return the number of header statements at the start of the given module body.

    The header is the leading run of string literal expressions (e.g. the module
    docstring) and `from __future__` imports, since they must come before any other code
    in a module.

    Args:
        body: The statements of a parsed module.
    """
    num_header = 0
    for statement in body:
        is_string = (
            isinstance(statement, ast.Expr)
            and isinstance(statement.value, ast.Constant)
            and isinstance(statement.value.value, str)
        )
        is_future_import = (
            isinstance(statement, ast.ImportFrom) and statement.module == "__future__"
        )
        if not (is_string or is_future_import):
            break
        num_header += 1
    return num_header


def _wrap_marked_block_in_tracer(
    tokens: asttokens.ASTTokens, start: Token, end: Token, filename: str
) -> Optional[ast.With]:
    """Wrap the statements between the "# pyta: snapshot-tracer-start" and
    "# pyta: snapshot-tracer-end" comments in a `with` block using the tracer named
    TRACER_ALIAS, and return the new `with` node. Mutates the parsed file, replacing the
    marked statements with the `with` block.

    Return None (and leave the tree unchanged) if there is no code between the comments, so
    that nothing is traced.

    Raise a SyntaxError pointing at the comment at fault if the code between the comments is
    not a run of whole statements in one block.

    Args:
        tokens: The tokens and parsed tree of the file.
        start: The snapshot-tracer-start comment token.
        end: The snapshot-tracer-end comment token, which comes after start.
        filename: The path to the file, used in error messages.
    """
    code = [
        tok
        for tok in tokens.tokens[start.index + 1 : end.index]
        if tok.type not in _NON_CODE_TOKEN_TYPES and tok.string != ";"
    ]
    if not code:
        return None

    # The start comment must be directly followed by a statement
    assert tokens.tree is not None  # parse=True always builds the tree
    location = _find_statement_starts(tokens.tree).get(code[0].index)
    if location is None:
        raise _comment_error(
            start, "snapshot-tracer-start must be directly followed by a statement", filename
        )

    # The end comment must directly follow a statement in the same block
    statements, first = location
    last = next(
        (
            i
            for i in range(first, len(statements))
            if statements[i].last_token.index == code[-1].index  # type: ignore[attr-defined]
        ),
        None,
    )
    if last is None:
        raise _comment_error(
            end,
            "snapshot-tracer-end must be in the same block as snapshot-tracer-start, "
            "right after a statement",
            filename,
        )

    wrapped = slice(first, last + 1)
    line, col = start.start
    with_node = _build_with_tracer_statement(statements[wrapped], line, col)
    statements[wrapped] = [with_node]
    return with_node


def _comment_error(tok: Token, msg: str, filename: str) -> SyntaxError:
    """Return a SyntaxError with the given message that points at the comment token tok.

    Args:
        tok: The comment token at fault.
        msg: The error message.
        filename: The path to the file, used in the error.
    """
    line, col = tok.start
    return SyntaxError(msg, (filename, line, col + 1, tok.line))


def _build_with_tracer_statement(body: list[ast.stmt], lineno: int, col_offset: int) -> ast.With:
    """Return a `with` statement using the tracer named TRACER_ALIAS that wraps the given
    statements, placed at the given line and column.

    Args:
        body: The statements to wrap. Must not be empty.
        lineno: The line number of the `with` statement.
        col_offset: The column of the `with` statement.
    """
    tracer_name = ast.Name(
        id=TRACER_ALIAS,
        ctx=ast.Load(),
        lineno=lineno,
        col_offset=col_offset,
        end_lineno=lineno,
        end_col_offset=col_offset,
    )
    return ast.With(
        items=[ast.withitem(context_expr=tracer_name)],
        body=body,
        lineno=lineno,
        col_offset=col_offset,
        end_lineno=body[-1].end_lineno,
        end_col_offset=body[-1].end_col_offset,
    )


def _find_statement_starts(tree: ast.AST) -> dict[int, tuple[list[ast.stmt], int]]:
    """Return a mapping from the index of each statement's first token (including any
    decorators) to the list of statements holding it and its index in that list.

    Args:
        tree: A tree parsed by asttokens, so each statement has a first_token.
    """
    starts = {}
    # Visit every node in the tree
    for node in ast.walk(tree):
        # Blocks of statements are stored in these fields on AST nodes
        for field in ("body", "orelse", "finalbody"):
            stmts = getattr(node, field, None)
            if isinstance(stmts, list):
                for index, stmt in enumerate(stmts):
                    starts[stmt.first_token.index] = (stmts, index)  # type: ignore[attr-defined]
    return starts
