import ast
import re
import tokenize
from dataclasses import dataclass

SNAPSHOT_MODULE = "python_ta.debug.snapshot"
SNAPSHOT_NAME = "snapshot"
SNAPSHOT_ALIAS = "_pyta_snapshot"

PATTERN = re.compile(r"#\s*pyta:\s*(snapshot\(.*\))\s*")


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

    snapshot_comments, tree = parse_with_snapshot_comments(path)
    print(f"Found {len(snapshot_comments)} snapshot comments in {path}")

    if not snapshot_comments:
        # code = compile(tree, filename=path, mode="exec")
        # exec(code, {"__name__": "__main__", "__file__": path})
        return

    insert_snapshot_import(tree)

    for comment in snapshot_comments:
        print(
            f"Found snapshot comment at line {comment.line}, column {comment.col}: {comment.snapshot_call} (inline: {comment.inline})"
        )

    # run the modified AST
    # tree.fix_missing_locations()
    # code = compile(tree, filename=path, mode="exec")
    # exec(code, {"__name__": "__main__", "__file__": path})


def parse_with_snapshot_comments(path: str) -> tuple[list[SnapshotComment], ast.Module]:
    """Get all snapshot comments in the given Python file.

    Args:
        path: The path to the Python file to search.

    Returns:
        A tuple containing:
            - A list of SnapshotComment objects for each snapshot comment found.
            - A parsed AST of the file.
    """
    comments = []

    with tokenize.open(path) as f:

        source = f.read()
        tree = ast.parse(source, filename=path)

        # Reset the file pointer to the beginning of the file
        f.seek(0)
        for tok in tokenize.generate_tokens(f.readline):
            if tok.type != tokenize.COMMENT:
                continue

            match = PATTERN.fullmatch(tok.string)
            if match:
                line, col = tok.start
                inline = bool(tok.line[:col].strip())
                comments.append(SnapshotComment(line, col, match.group(1), inline))

    return comments, tree


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
    tree.body.insert(0, import_node)


def insert_snapshot_call(tree: ast.AST, snapshot_comment: SnapshotComment) -> None:
    """Insert a snapshot call at the given line and column in the AST.

    Args:
        tree: The AST to modify.
        snapshot_comment: The snapshot comment to insert.
    """
    snapshot_node = parse_snapshot_call(snapshot_comment.snapshot_call)
    expr_node = ast.Expr(value=snapshot_node)

    if snapshot_comment.inline:
        pass
    else:
        pass


def _standalone_block(
    body: list[ast.stmt], line: int, col: int, lines: list[str]
) -> list[ast.stmt]:
    """Return the statement list a comment on its own line belongs to, by indentation."""
    if col <= body[0].col_offset:
        return body

    owner = None
    for stmt in body:
        if stmt.lineno < line:
            owner = stmt

    chosen = None
    for header, block in (_child_blocks(owner, lines) if owner else []):
        if header < line:
            chosen = block
    if chosen is None:
        raise IndentationError(f"line {line}: snapshot comment doesn't line up with any block")

    return _standalone_block(chosen, line, col, lines)


def _child_blocks(stmt: ast.stmt, lines: list[str]) -> list[tuple[int, list[ast.stmt]]]:
    """Return (header line, statement list) for each block inside a compound statement."""
    blocks = []

    # Add the main body of the statement, if it has one
    # if getattr(stmt, "body", None) and isinstance(stmt.body[0], ast.stmt):
    #     blocks.append((stmt.lineno, stmt.body))

    # Add any except handlers, if the statement is a try statement
    # for handler in getattr(stmt, "handlers", []):
    #     blocks.append((handler.lineno, handler.body))

    # Add any case blocks, if the statement is a match statement
    for case in getattr(stmt, "cases", []):
        blocks.append((case.pattern.lineno, case.body))

    # Add any else or finally blocks
    # else / finally aren't nodes, so their header is the first line of code after the previous block ends

    return sorted(blocks, key=lambda b: b[0])
