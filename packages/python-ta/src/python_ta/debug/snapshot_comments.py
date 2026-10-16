import ast
import re
import tokenize

import asttokens
from asttokens.util import Token, replace

from .snapshot import snapshot

SNAPSHOT_NAME = "snapshot"

# Note that same length as shortest prefix  "#pyta:snapshot"
SNAPSHOT_ALIAS = "__snapshot__"

PATTERN = re.compile(r"#\s*pyta:\s*(snapshot\(.*\))\s*")

# Statements that leave their block, so a snapshot call placed after them would never run
_EXITS = {ast.Return: "return", ast.Raise: "raise", ast.Break: "break", ast.Continue: "continue"}


def run_with_snapshot_comments(path: str) -> None:
    """Run the given Python file with snapshot comments enabled.

    Args:
        path: The path to the Python file to run.
    """
    with tokenize.open(path) as f:
        source = f.read()

    try:
        code = compile(insert_snapshot_calls(source, path), filename=path, mode="exec")
    except SyntaxError as e:
        # Show the line as the user wrote it, not with the inserted snapshot call
        if e.lineno:
            e.text = source.splitlines(keepends=True)[e.lineno - 1]
        raise

    exec(code, {"__name__": "__main__", "__file__": path, SNAPSHOT_ALIAS: snapshot})


def insert_snapshot_calls(source: str, filename: str = "<unknown>") -> str:
    """Return the given source with each snapshot comment replaced by a snapshot call.

    Each call replaces its comment on the same line.

    Args:
        source: The Python source code.
        filename: The filename to report in syntax errors.
    """
    atok = asttokens.ASTTokens(source, parse=True, filename=filename)
    assert atok.tree is not None  # parse=True always builds the tree

    # Map from index of last token to statement node, for finding which statement an inline comment follows
    stmt_ends = {
        node.last_token.index: node  # type: ignore[attr-defined]  # added by asttokens
        for node in ast.walk(atok.tree)
        if isinstance(node, ast.stmt) and not hasattr(node, "body")
    }

    # Find all snapshot comments and replace them with snapshot calls
    edits = [
        _edit(atok, tok, stmt_ends, filename)
        for tok in atok.tokens
        if tok.type == tokenize.COMMENT and PATTERN.fullmatch(tok.string)
    ]
    return replace(source, edits)


def _edit(
    atok: asttokens.ASTTokens, tok: Token, stmt_ends: dict[int, ast.stmt], filename: str
) -> tuple[int, int, str]:
    """Return the (start, end, text) edit that turns the snapshot comment tok into a snapshot call."""
    match = PATTERN.fullmatch(tok.string)
    assert match is not None  # only called on snapshot comments
    line, col = tok.start

    def error(msg: str) -> SyntaxError:
        return SyntaxError(msg, (filename, line, col + 1, tok.line))

    if not _is_snapshot_call(match.group(1)):
        raise error(f"invalid snapshot comment: {match.group(1)}")

    # If the snapshot comment is on a line by itself
    if not tok.line[:col].strip():
        replacement = SNAPSHOT_ALIAS
    else:
        prev = atok.prev_token(tok)
        stmt = stmt_ends.get(prev.index)
        if prev.string == ":":
            raise error("a snapshot comment can't go on a line ending in ':'")
        if stmt is None:
            raise error("an inline snapshot comment must follow a complete statement")
        if type(stmt) in _EXITS:
            raise error(f"a snapshot comment after '{_EXITS[type(stmt)]}' would never run")
        replacement = "; " + SNAPSHOT_ALIAS

    # Replace everything up to the call's "(", padded so the arguments don't move
    prefix_len = match.start(1) + len(SNAPSHOT_NAME)
    return tok.startpos, tok.startpos + prefix_len, replacement.ljust(prefix_len)


def _is_snapshot_call(call: str) -> bool:
    """Return whether the given string is a single call to snapshot."""
    try:
        tree = ast.parse(call, mode="eval")
    except SyntaxError:
        return False

    return (
        isinstance(tree.body, ast.Call)
        and isinstance(tree.body.func, ast.Name)
        and tree.body.func.id == SNAPSHOT_NAME
    )
