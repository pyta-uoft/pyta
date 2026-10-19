import ast
import re
import tokenize

import asttokens
from asttokens.util import Token, replace

from .snapshot import snapshot

SNAPSHOT_NAME = "snapshot"

SNAPSHOT_ALIAS = "__snapshot__"

PATTERN = re.compile(r"#\s*pyta:\s*(snapshot\(.*\))\s*")


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

    tokens = asttokens.ASTTokens(source, parse=True, filename=path)
    assert tokens.tree is not None  # parse=True always builds the tree

    # Indices of the last token of each statement, for checking that an inline comment follows one
    stmt_ends = {
        node.last_token.index  # type: ignore[attr-defined]  # added by asttokens
        for node in ast.walk(tokens.tree)
        if isinstance(node, ast.stmt)
    }

    # Find all snapshot comments and replace them with snapshot calls
    edits = [
        _edit(tokens, tok, match, stmt_ends, path)
        for tok in tokens.tokens
        if tok.type == tokenize.COMMENT and (match := PATTERN.fullmatch(tok.string))
    ]
    return replace(source, edits)


def _edit(
    tokens: asttokens.ASTTokens,
    tok: Token,
    match: re.Match[str],
    stmt_ends: set[int],
    filename: str,
) -> tuple[int, int, str]:
    """Return the (start, end, text) edit that turns the snapshot comment tok into a snapshot call."""
    line, col = tok.start

    def error(msg: str) -> SyntaxError:
        return SyntaxError(msg, (filename, line, col + 1, tok.line))

    if not _is_snapshot_call(match.group(1)):
        raise error(f"invalid snapshot comment: {match.group(1)}")

    # If the snapshot comment is on a line by itself
    if col == 0 or tok.line[:col].isspace():
        replacement = SNAPSHOT_ALIAS
    else:
        prev = tokens.prev_token(tok)
        if prev.index not in stmt_ends:
            raise error("an inline snapshot comment must follow a complete statement")
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
