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


def run_with_snapshots(path: str) -> None:
    """Run the given Python file with snapshot comments enabled.

    Args:
        path: The path to the Python file to run.
    """
    code = compile(transform_snapshot_comments(path), filename=path, mode="exec")
    exec(code, {"__name__": "__main__", "__file__": path, SNAPSHOT_ALIAS: snapshot})


def transform_snapshot_comments(path: str) -> str:
    """Return the source of the given Python file with each snapshot comment replaced by a snapshot call.

    Each call replaces its comment on the same line.

    Args:
        path: The path to the Python file to transform.
    """
    with tokenize.open(path) as f:
        source = f.read()

    atok = asttokens.ASTTokens(source, parse=True, filename=path)
    assert atok.tree is not None  # parse=True always builds the tree

    # Map from index of last token to statement node, for finding which statement an inline comment follows
    stmt_ends = {
        node.last_token.index: node  # type: ignore[attr-defined]  # added by asttokens
        for node in ast.walk(atok.tree)
        if isinstance(node, ast.stmt) and not hasattr(node, "body")
    }

    # Find all snapshot comments and replace them with snapshot calls
    comments = [
        tok for tok in atok.tokens if tok.type == tokenize.COMMENT and PATTERN.fullmatch(tok.string)
    ]
    new_source = replace(source, [_edit(atok, tok, stmt_ends, path) for tok in comments])

    # The source parsed before the calls were inserted, so any error here was caused by a
    # snapshot comment. Report it at the last snapshot comment at or before the error line.
    try:
        ast.parse(new_source, filename=path)
    except SyntaxError as e:
        culprits = [tok for tok in comments if e.lineno and tok.start[0] <= e.lineno]
        if not culprits:
            raise
        line, col = culprits[-1].start
        raise SyntaxError(
            "snapshot comment can't go here (check its indentation)",
            (path, line, col + 1, culprits[-1].line),
        ) from None

    return new_source


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
