import ast
import re
import tokenize
from dataclasses import dataclass

from .snapshot import ROOT_FRAME_MARKER

SNAPSHOT_MODULE = "python_ta.debug.snapshot"
SNAPSHOT_NAME = "snapshot"
SNAPSHOT_ALIAS = "__pyta_snapshot__"

PATTERN = re.compile(r"#\s*pyta:\s*(snapshot\(.*\))\s*")

# Tokens that don't count as code when finding which lines contain code
_NON_CODE_TOKENS = {
    tokenize.COMMENT,
    tokenize.NL,
    tokenize.NEWLINE,
    tokenize.INDENT,
    tokenize.DEDENT,
    tokenize.ENDMARKER,
}


@dataclass
class SnapshotComment:
    """A snapshot comment in a Python file.

    Attributes:
        line: The line number of the comment.
        col: The column number of the comment.
        snapshot_call: The snapshot call string.
        inline: Whether the comment is inline or not.
    """

    line: int
    col: int
    snapshot_call: str
    inline: bool


def run_with_snapshot_comments(path: str) -> None:
    """Run the given Python file with snapshot comments enabled.

    Args:
        path: The path to the Python file to run.
    """
    snapshot_comments, tree, code_lines = parse_with_snapshot_comments(path)

    if snapshot_comments:
        for comment in snapshot_comments:
            insert_snapshot_call(tree, comment, code_lines)

        insert_snapshot_import(tree)
        ast.fix_missing_locations(tree)

    code = compile(tree, filename=path, mode="exec")
    # Mark the file's module as the outermost frame, so snapshot() doesn't capture the frames that ran it
    exec(code, {"__name__": "__main__", "__file__": path, ROOT_FRAME_MARKER: True})


def parse_with_snapshot_comments(path: str) -> tuple[list[SnapshotComment], ast.Module, set[int]]:
    """Get all snapshot comments in the given Python file.

    Args:
        path: The path to the Python file to search.

    Returns:
        A tuple containing:
            - A list of SnapshotComment objects for each snapshot comment found.
            - A parsed AST of the file.
            - The set of line numbers that contain code (not just comments or blank space).
    """
    comments = []
    code_lines: set[int] = set()

    with tokenize.open(path) as f:

        source = f.read()
        tree = ast.parse(source, filename=path)

        # Reset the file pointer to the beginning of the file
        f.seek(0)
        for tok in tokenize.generate_tokens(f.readline):
            if tok.type not in _NON_CODE_TOKENS:
                code_lines.update(range(tok.start[0], tok.end[0] + 1))
                continue
            if tok.type != tokenize.COMMENT:
                continue

            match = PATTERN.fullmatch(tok.string)
            if match:
                line, col = tok.start
                inline = bool(tok.line[:col].strip())
                comments.append(SnapshotComment(line, col, match.group(1), inline))

    return comments, tree, code_lines


def parse_snapshot_call(snapshot_call: str) -> ast.Call:
    """Parse a snapshot call string into an AST node.

    Args:
        snapshot_call: The snapshot call string to parse.

    Returns:
        An AST node representing the snapshot call.
    """
    tree = ast.parse(snapshot_call, mode="eval")

    if not (
        isinstance(tree.body, ast.Call)
        and isinstance(tree.body.func, ast.Name)
        and tree.body.func.id == SNAPSHOT_NAME
    ):
        raise ValueError(f"Invalid snapshot call: {snapshot_call}")

    return tree.body


def insert_snapshot_import(tree: ast.Module) -> None:
    """Insert an import statement for the snapshot function at the top of the AST.

    Args:
        tree: The AST to modify.
    """
    import_node = ast.ImportFrom(
        module=SNAPSHOT_MODULE,
        names=[ast.alias(name=SNAPSHOT_NAME, asname=SNAPSHOT_ALIAS)],
        level=0,
    )
    # A module docstring and `from __future__` imports must stay at the top of the file
    index = 1 if ast.get_docstring(tree, clean=False) is not None else 0
    for stmt in tree.body[index:]:
        if not (isinstance(stmt, ast.ImportFrom) and stmt.module == "__future__"):
            break
        index += 1
    tree.body.insert(index, import_node)


def insert_snapshot_call(
    tree: ast.Module, snapshot_comment: SnapshotComment, code_lines: set[int]
) -> None:
    """Insert a snapshot call at the given line and column in the AST.

    Args:
        tree: The AST to modify.
        snapshot_comment: The snapshot comment to insert.
        code_lines: The set of line numbers that contain code.
    """
    snapshot_node = parse_snapshot_call(snapshot_comment.snapshot_call)
    snapshot_node.func = ast.Name(id=SNAPSHOT_ALIAS, ctx=ast.Load())
    expr_node = ast.Expr(value=snapshot_node)

    # Report errors raised by the snapshot call at the comment's position
    for node in ast.walk(expr_node):
        if isinstance(node, (ast.expr, ast.stmt)):
            node.lineno = node.end_lineno = snapshot_comment.line
            node.col_offset = node.end_col_offset = snapshot_comment.col

    if snapshot_comment.inline:
        pass
    else:
        block = _standalone_block(
            tree.body, snapshot_comment.line, snapshot_comment.col, code_lines
        )
        # The comment runs just before the first statement that comes after it
        index = next(
            (i for i, stmt in enumerate(block) if stmt.lineno > snapshot_comment.line),
            len(block),
        )
        block.insert(index, expr_node)


def _standalone_block(
    body: list[ast.stmt], line: int, col: int, code_lines: set[int]
) -> list[ast.stmt]:
    """Return the statement list a comment on its own line belongs to, by indentation."""
    if not body or col <= body[0].col_offset:
        return body

    owner = None
    for stmt in body:
        if stmt.lineno >= line:
            break
        owner = stmt

    chosen = None
    for header, block in (_child_blocks(owner, code_lines) if owner else []):
        if header < line:
            chosen = block
    if chosen is None:
        raise IndentationError(f"line {line}: snapshot comment doesn't line up with any block")

    return _standalone_block(chosen, line, col, code_lines)


def _child_blocks(stmt: ast.stmt, code_lines: set[int]) -> list[tuple[int, list[ast.stmt]]]:
    """Return (header line, statement list) for each block inside a compound statement."""
    blocks = []

    # Add the main body of the statement, if it has one
    body = getattr(stmt, "body", None)
    if body and isinstance(body[0], ast.stmt):
        blocks.append((stmt.lineno, body))

    # Add any except handlers, if the statement is a try statement
    handlers = getattr(stmt, "handlers", [])
    for handler in handlers:
        blocks.append((handler.lineno, handler.body))

    # Add any case blocks, if the statement is a match statement
    for case in getattr(stmt, "cases", []):
        blocks.append((case.pattern.lineno, case.body))

    # Add any else or finally blocks
    # else / finally aren't nodes, so their header is the first line of code after the previous block ends
    before_else = handlers[-1].body if handlers else body or []

    orelse = getattr(stmt, "orelse", [])
    if orelse:
        header = _first_code_line(code_lines, before_else[-1].end_lineno, orelse[0].lineno)
        if len(orelse) == 1 and isinstance(orelse[0], ast.If) and orelse[0].lineno == header:
            # An elif is stored as an If inside orelse, starting on the header line itself
            blocks.extend(_child_blocks(orelse[0], code_lines))
        else:
            blocks.append((header, orelse))

    finalbody = getattr(stmt, "finalbody", [])
    if finalbody:
        before_finally = orelse or before_else
        header = _first_code_line(code_lines, before_finally[-1].end_lineno, finalbody[0].lineno)
        blocks.append((header, finalbody))

    return sorted(blocks, key=lambda b: b[0])


def _first_code_line(code_lines: set[int], after: int, upto: int) -> int:
    """Return the first line in (after, upto] that contains code."""
    return next(lineno for lineno in range(after + 1, upto + 1) if lineno in code_lines)
